(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes

(* jchsys *)
open JCHPrintUtils

(* jchpoly *)
open JCHLinearConstraint

let dbg = ref false

let params = JCHAnalysisUtils.numeric_params

(* No projections, just removes the columns *)
let remove_dimensions
      (new_nvars:int) (m:big_int array array) unsorted_cs =
  let new_ncols = succ new_nvars in
  let sorted_cs = List.sort compare unsorted_cs in
  let remove_dim_a a new_a =
    new_a.(new_nvars) <- a.(pred (Array.length a));
    let rec remove old_c new_c cs =
      if new_c < new_nvars then
	match cs with
	| c :: rest_cs ->
	    if old_c = c then remove (succ old_c) new_c rest_cs
	    else
	      begin
		new_a.(new_c) <- a.(old_c);
		remove (succ old_c) (succ new_c) cs
	      end
	| _ ->
	    new_a.(new_c) <- a.(old_c);
	    remove (succ old_c) (succ new_c) [] in
    remove 0 0 sorted_cs in
  let nrows = Array.length m in
  let new_m = Array.make_matrix nrows new_ncols zero_big_int in
  begin
    for i = 0 to pred nrows do
      remove_dim_a m.(i) new_m.(i)
    done;
    new_m
  end

let add_dims_and_embed (dimsup:int) (m:big_int array array) =
  let nrows = Array.length m in
  if dimsup < 0 then
    raise (JCHAnalysisUtils.numeric_params#analysis_failed
             2 "programming error: add_dims_and_embed - negaive extra dimension")
  else if dimsup = 0 then
    m
  else if nrows = 0 then
    m
  else
    let ncols = Array.length m.(0) in
    let new_ncols = ncols + dimsup in
    let new_m = Array.make_matrix nrows new_ncols zero_big_int in
    begin
      for i = 0 to pred nrows do
        let a = m.(i) in
        let new_a = new_m.(i) in
        for j = 0 to ncols - 2 do
	  new_a.(j) <- a.(j)
        done;
        new_a.(pred new_ncols) <- a.(pred ncols)
      done;
      new_m
    end

(* map is a list of (old_col, new_col) and the result switches the columns
 * old_index with new_index *)
let remap_m nvars (map: (int * int) list) m =
  let remap_a (a: big_int array) (new_a: big_int array) =
    let change (old_i, new_i) =
      new_a.(new_i) <- a.(old_i) in
    List.iter change map;
    new_a.(nvars) <- a.(nvars) in (* set the constant *)
  let nrows = Array.length m in
  let new_m = Array.make_matrix nrows (succ nvars) zero_big_int in
  begin
    for i = 0 to pred nrows do
      remap_a m.(i) new_m.(i);
    done;
    new_m
  end

(* remove last n variable columns. *)
let remove_last_cols_m n m =
  let nrows = Array.length m in
  if n = 0 || nrows = 0 then
    m
  else
    let nvars = pred (Array.length m.(0)) in
    let new_nvars = nvars - n in
    let new_m = Array.make_matrix nrows (succ new_nvars) zero_big_int in
    begin
      for i = 0 to pred nrows do
        let a = m.(i) in
        let new_a = new_m.(i) in
        for j = 0 to pred new_nvars do
	  new_a.(j) <- a.(j)
        done;
        new_a.(new_nvars) <- a.(nvars) (* constant column *)
      done;
      new_m
    end

(* var = var + const *)
(* Add (coeff of var) * (-const) to the constant *)
let increment_m m c const =
  let nrows = Array.length m in
  if nrows = 0 then
    m
  else
    let ncols = Array.length m.(0) in
    let neg_const = minus_big_int const in
    let const_col = pred ncols in
    let new_m = Array.make_matrix nrows ncols zero_big_int in
    begin
      for i = 0 to pred nrows do
	let a = m.(i) in
	new_m.(i) <- Array.copy a;
	let coeff = a.(c) in
	if not (eq_big_int coeff zero_big_int) then
	  let new_const =
            add_big_int (mult_big_int coeff neg_const) a.(const_col) in
	  new_m.(i).(const_col) <- new_const
      done;
      new_m
    end


let empty_matrix = Array.make_matrix 0 0 zero_big_int

let poly_index = ref (-1)
let get_poly_index () =
  incr poly_index;
  !poly_index

module ConstraintCollections = CHCollections.Make (
  struct
    type t = linear_constraint_t
    let compare c1 c2 = c1#compare c2
    let toPretty c = c#toPretty
  end)

(* It keeps the size minimal by removing columns that are not used
 * The only exception when poly_inds is larger is for polys used in a call
 * or in intermediate stages: after an augment operation, ... *)
class poly_t =
  object (self: 'a)

    val bottom = false
    val top = true

    (* list of indices used in poly, sorted from small_to large *)
    val poly_inds = []

    (* list of pairs of indices (poly column -> PolyIntervalArray index); sorted *)
    val index_map = []
    val eq_matrix = empty_matrix
    val ineq_matrix = empty_matrix
    val poly_ind = get_poly_index()

    method is_bottom = bottom
    method is_top = top
    method get_poly_inds = poly_inds
    method get_index_map = index_map
    method get_eq_matrix = eq_matrix
    method get_ineq_matrix = ineq_matrix

    method private get_poly_dim = List.length index_map
    method private get_column ind =
      try
	fst (List.find (fun (_, j) -> j = ind) index_map)
      with
	Not_found ->
	raise (JCH_failure
                 (LBLOCK [STR "Column "; INT ind;
			  STR " not found in JCHPoly.get_column"]))

    method private is_in_poly ind =
      let rec find is =
	match is with
	| i :: rest_is ->
	    if i < ind then find rest_is
	    else i = ind
	| [] -> false in
      find poly_inds

    method mk_poly poly_inds index_map eq_m ineq_m =
      {< poly_inds = poly_inds;
	index_map = index_map;
	bottom = false; top = false;
	eq_matrix = eq_m; ineq_matrix = ineq_m;
	poly_ind = get_poly_index() >}

    method remove_trivial_ineqs =
      let constrs = self#get_constraints in
      let red_constrs = List.filter (fun c -> not c#is_0_geq_0) constrs in
      self#mk_poly_from_constraints false red_constrs

    method copy =
      {< eq_matrix = JCHArrayUtils.copy_m eq_matrix;
         ineq_matrix = JCHArrayUtils.copy_m ineq_matrix;
         poly_ind = get_poly_index()
      >}

    method clone = {< >}

    method private _record_number_constraints constrs =
      JCHAnalysisUtils.numeric_params#record_number_constraints
        (List.length constrs)

    method get_constraints =
      if top || bottom then []
      else
	let constrs =
          (linear_constraints_of_matrix
             true eq_matrix) @ (linear_constraints_of_matrix false ineq_matrix) in
	self#_record_number_constraints constrs;
	List.map (fun constr -> constr#remap index_map) constrs

    method change_inds old_ind_to_new_ind =
      let new_index_map =
        List.map (fun (c,i) -> (c, List.assoc i old_ind_to_new_ind)) index_map in
      let new_poly_inds = List.sort compare (List.map snd new_index_map)  in
      {< poly_inds = new_poly_inds;
         index_map = new_index_map;
         poly_ind = get_poly_index()
      >}

    method mk_bottom =
      {< bottom = true;
         top = false;
         poly_inds = [];
         index_map = [];
	 eq_matrix = empty_matrix;
         ineq_matrix = empty_matrix;
         poly_ind = get_poly_index()
      >}

    method mk_top =
      {< bottom = false;
         top = true;
         poly_inds = [];
         index_map = [];
	 eq_matrix = empty_matrix;
         ineq_matrix = empty_matrix;
         poly_ind = get_poly_index()
      >}

    (* This is just for calls which have more variables than the ones with
     * constraints in chpoly *)
    method mk_top_large new_poly_inds new_index_map =
      {< bottom = false;
         top = true;
         poly_inds = new_poly_inds;
         index_map = new_index_map;
	 eq_matrix = empty_matrix;
         ineq_matrix = empty_matrix;
         poly_ind = get_poly_index()
      >}

    method private mk_poly_
                     new_poly_inds new_index_map new_eq_matrix new_ineq_matrix =
      if List.length new_poly_inds <> List.length new_index_map then
        raise (JCHAnalysisUtils.numeric_params#analysis_failed
                 2 "programming error: mk_top_large - index_map and poly_inds of different lengths");
      {< bottom = false;
         top = false;
         poly_inds = new_poly_inds;
         index_map = new_index_map;
	 eq_matrix = new_eq_matrix;
         ineq_matrix = new_ineq_matrix;
         poly_ind = get_poly_index()
      >}

    method private get_used_indices' (a: 'a) =
      let map = a#get_index_map in
      List.map snd map

    method private get_poly_dim' (a: 'a) =
      let map = a#get_index_map in
      List.length map

    method private get_column_ index_map' ind =
      try
	fst (List.find (fun (_, j) -> j = ind) index_map')
      with
	Not_found ->
	raise (JCH_failure
                 (LBLOCK [STR "Column "; INT ind;
			  STR " not found in JCHPoly.get_column"]))

    method private make_index_map inds =
      let inds = List.sort compare inds in
      let add_index_to_map (i, res) ind = (i + 1, (i, ind) :: res) in
      let (_, map) = List.fold_left add_index_to_map (0, []) inds in
      List.rev map

    method private get_used_indices_in_constrs constrs =
      let used_indices = new IntCollections.set_t in
      let add_constr constr =
	used_indices#addList constr#get_used_indices in
      List.iter add_constr constrs;
      used_indices#toList

    (* used cols sorted *)

    method private get_used_cols (a: 'a) =
      let eq_m = a#get_eq_matrix in
      let ineq_m = a#get_ineq_matrix in
      let used_cols = new IntCollections.set_t in
      let add_used_cols_a a =
	for i = 0 to (Array.length a) - 2 do
	  if not (eq_big_int a.(i) zero_big_int) then used_cols#add i
	done in
      for i = 0 to pred (Array.length eq_m) do
	add_used_cols_a eq_m.(i)
      done;
      for i = 0 to pred (Array.length ineq_m) do
	add_used_cols_a ineq_m.(i)
      done;
      List.sort compare used_cols#toList

    method is_used_ind ind =
      try
	let col = self#get_column ind in
	try
	  for i = 0 to pred (Array.length eq_matrix) do
	    if not (eq_big_int eq_matrix.(i).(col) zero_big_int) then raise Exit
	  done;
	  for i = 0 to pred (Array.length ineq_matrix) do
	    if not (eq_big_int ineq_matrix.(i).(col) zero_big_int) then raise Exit
	  done;
	  false
	with Exit -> true
      with _ -> false

    (* It removes columns that are not used *)
    method private reduce (a: 'a) =
      if a#is_bottom then a#mk_bottom
      else if a#is_top then a#mk_top
      else
	let used_cols = self#get_used_cols a in
	let new_poly_inds =
          List.map (fun c -> List.assoc c a#get_index_map) used_cols in
	let new_poly_dim = List.length new_poly_inds in
	if new_poly_dim = self#get_poly_dim' a then a#clone
	else
	  begin
	    let unused_cols =
	      let add_unused res (i,_) =
		if List.mem i used_cols then res
		else i :: res in
	      List.fold_left add_unused [] a#get_index_map
	    in
	    let new_index_map = self#make_index_map new_poly_inds in
	    let new_eq_matrix =
              remove_dimensions new_poly_dim a#get_eq_matrix unused_cols in
	    let new_ineq_matrix =
              JCHArrayUtils.remove_trivial_rows
                (remove_dimensions new_poly_dim a#get_ineq_matrix unused_cols) in
	    if Array.length new_eq_matrix = 0
               && Array.length new_ineq_matrix = 0 then
              self#mk_top
	    else
	      {< bottom = false;
                 top = false;
                 poly_inds = new_poly_inds;
                 index_map = new_index_map;
		 eq_matrix = new_eq_matrix;
                 ineq_matrix = new_ineq_matrix;
                 poly_ind = get_poly_index()
              >}
	  end

    (* It adds columns to the handle
     * These columns correspod to variables in the poly but which are not in
     * the handle
     * new_inds is a super-set of the used indices in index_map *)
    method private augment new_poly_inds new_index_map (a: 'a) =
      if a#is_bottom then a#mk_bottom
      else
	let res_dim = List.length new_index_map in
	let aindex_map = a#get_index_map in
	let adim = List.length aindex_map in
	let extra_dim = res_dim - adim in
	let add_to_map (i, map) (new_col, index) =
	  try
	    let old_col = self#get_column_ aindex_map index in
	    (i, (old_col, new_col) :: map)
	  with _ -> (i+1, (i, new_col) :: map) in
	let (_, map) = List.fold_left add_to_map (adim, []) new_index_map in
	let big_eq_matrix = add_dims_and_embed extra_dim  a#get_eq_matrix in
	let big_ineq_matrix = add_dims_and_embed extra_dim  a#get_ineq_matrix in

	let new_eq_matrix = remap_m res_dim map big_eq_matrix in
	let new_ineq_matrix = remap_m res_dim map big_ineq_matrix in
	{< bottom = false;
           top = false;
           poly_inds = new_poly_inds;
           index_map = new_index_map;
	   eq_matrix = new_eq_matrix;
           ineq_matrix = new_ineq_matrix;
           poly_ind = get_poly_index()
        >}

   (* inds1 and inds2 are sorted lists
    * It produces a sorted list *)
    method private find_common_inds inds1 inds2 =
      let rec add_ind res is1 is2 =
	match (is1, is2) with
	| (i1 :: rest_is1, i2 :: rest_is2) ->
	    if i1 = i2 then add_ind (i1 :: res) rest_is1 rest_is2
	    else if i1 < i2 then add_ind (i1 :: res) rest_is1 is2
	    else add_ind (i2 :: res) is1 rest_is2
	| (i1 :: rest_is1, []) -> add_ind (i1 :: res) rest_is1 []
	| ([], i2 :: rest_is2) -> add_ind (i2 :: res) [] rest_is2
	| ([], []) -> List.rev res in
      add_ind [] inds1 inds2

    method private augment_both (s: 'a) (a: 'a) =
      let common_inds =
        self#find_common_inds
          (self#get_used_indices' s) (self#get_used_indices' a) in
      let new_index_map = self#make_index_map common_inds in
      let s_aug = self#augment common_inds new_index_map s in
      let a_aug = self#augment common_inds new_index_map a in
      (common_inds, new_index_map, s_aug, a_aug)

    method private is_included_in a b =
      let a_eqs = a#get_eq_matrix in
      let a_ineqs = a#get_ineq_matrix in
      let b_eqs = b#get_eq_matrix in
      let b_ineqs = b#get_ineq_matrix in
      try
	for i = 0 to pred (Array.length b_eqs) do
	  let res = JCHArrayUtils.implies_constraint a_eqs a_ineqs b_eqs.(i) true in
	  if not (fst res) then raise Exit
	done;
	for i = 0 to pred (Array.length b_ineqs) do
	  let res =
            JCHArrayUtils.implies_constraint a_eqs a_ineqs b_ineqs.(i) false in
	  if not (fst res) then
	      raise Exit
	done;
	true
      with _ -> false

    method equal (a: 'a) =
      match (bottom, a#is_bottom, top, a#is_top) with
      |	(true, true, _, _) -> true
      |	(_, _, true, true) -> true
      |	(false, false, false, false) ->
	  let (_, _, s_aug, a_aug) = self#augment_both self a in
	  self#is_included_in s_aug a_aug && self#is_included_in a_aug s_aug
      |	_ -> false

    method leq (a: 'a) =
      match (bottom, a#is_bottom, top, a#is_top) with
      |	(true, _, _, _) -> true
      |	(_, true, _, _) -> false
      |	(_, _, _, true) -> true
      |	(_, _, true, _) -> false
      |	_ ->
	 let (_, _, s_aug, a_aug) = self#augment_both self a in
	 self#is_included_in s_aug a_aug

    method private minimize_ new_poly_inds new_index_map eq_m ineq_m =
      if Array.length eq_m = 0 && Array.length ineq_m = 0 then self#mk_top
      else
	match JCHArrayUtils.minimize_m eq_m ineq_m with
	| Some (eq'_m, ineq'_m) ->
	   if Array.length eq'_m = 0 && Array.length ineq'_m = 0 then
             self#mk_top
	   else
             {< bottom = false;
                top = false;
                poly_inds = new_poly_inds;
                index_map = new_index_map;
		eq_matrix = eq'_m;
                ineq_matrix = ineq'_m;
                poly_ind = get_poly_index()
             >}
	| _ -> self#mk_bottom

   method minimize =
     self#minimize_ poly_inds index_map eq_matrix ineq_matrix

    method meet (a: 'a) : 'a =
      match (bottom, a#is_bottom, top, a#is_top) with
      | (true, _, _, _)
      | (_, true, _, _) -> self#mk_bottom
      | (_, _, true, _) -> a#copy
      | (_, _, _, true) -> self#copy
      | _ ->
	 let (new_poly_inds, new_index_map, s_aug, a_aug) =
           self#augment_both self a in
	  let new_eq_m = Array.append s_aug#get_eq_matrix a_aug#get_eq_matrix in
	  let new_ineq_m =
            Array.append s_aug#get_ineq_matrix a_aug#get_ineq_matrix in
	  self#minimize_ new_poly_inds new_index_map new_eq_m new_ineq_m

    method meet_simple (a: 'a) : 'a =
      match (bottom, a#is_bottom, top, a#is_top) with
      | (true, _, _, _)
      | (_, true, _, _) -> self#mk_bottom
      | (_, _, true, _) -> a#copy
      | (_, _, _, true) -> self#copy
      | _ ->
	 let (new_poly_inds, new_index_map, s_aug, a_aug) =
           self#augment_both self a in
	  let new_eq_m = Array.append s_aug#get_eq_matrix a_aug#get_eq_matrix in
	  let new_ineq_m =
            Array.append s_aug#get_ineq_matrix a_aug#get_ineq_matrix in
	  {< bottom = false;
             top = false;
             poly_inds = new_poly_inds;
             index_map = new_index_map;
	     eq_matrix = new_eq_m;
             ineq_matrix = new_ineq_m;
             poly_ind = get_poly_index()
          >}

    method private join_same_vars (s_aug: 'a) (a_aug: 'a) =
      let (sbrays, surays, _) =
        JCHArrayUtils.find_ineq_sols_m
          true s_aug#get_eq_matrix s_aug#get_ineq_matrix in
      let (abrays, aurays, _) =
        JCHArrayUtils.find_ineq_sols_m
          true a_aug#get_eq_matrix a_aug#get_ineq_matrix in
      let brays = Array.append sbrays abrays in
      let urays = Array.append surays aurays in
      let (join_eqs, join_ineqs, _) =
        JCHArrayUtils.find_ineq_sols_m false brays urays in
      let join_ineqs = JCHArrayUtils.remove_trivial_rows join_ineqs in
      (join_eqs, JCHArrayUtils.remove_trivial_rows join_ineqs)

    method join (a: 'a) =
      match (bottom, a#is_bottom, top, a#is_top) with
      | (true, _, _, _) -> a#copy
      | (_, true, _, _) -> self#copy
      | (_, _, true, _)
      | (_, _, _, true) -> self#mk_top
      | _ ->
	 let (new_poly_inds, new_index_map, s_aug, a_aug) =
           self#augment_both self a in
	  let (join_eqs, join_ineqs) = self#join_same_vars s_aug a_aug in
	  if Array.length join_eqs = 0
             && Array.length join_ineqs = 0 then
            self#mk_top
	  else
	    let p = {< poly_inds = new_poly_inds;
		       index_map = new_index_map;
		       eq_matrix = join_eqs;
                       ineq_matrix = join_ineqs;
		       poly_ind = get_poly_index() >} in
	    self#reduce p

    method widening (a: 'a) =
      match (bottom, a#is_bottom, top, a#is_top) with
      | (true, _, _, _) -> a#copy
      | (_, true, _, _) -> self#copy
      | (_, _, true, _)
      | (_, _, _, true) -> self#mk_top
      | _ ->
	 let (new_poly_inds, new_index_map, s_aug, a_aug) =
           self#augment_both self a in

	 let (j_eqs, j_ineqs) = self#join_same_vars s_aug a_aug in
	 if Array.length j_eqs = 0 && Array.length j_ineqs = 0 then
           self#mk_top
	  else
	    begin
	      let s_aug_eqs = s_aug#get_eq_matrix in
	      let s_aug_ineqs = s_aug#get_ineq_matrix in
	      let a_aug_eqs = a_aug#get_eq_matrix in
	      let a_aug_ineqs = a_aug#get_ineq_matrix in
	      let new_eqs = ref [] in
	      let new_ineqs = ref [] in
	      let check_constraint is_eq eqs ineqs _r c =
		let (implies, res_opt) =
                  JCHArrayUtils.implies_constraint eqs ineqs c is_eq in
		if not implies then
		  begin
		    if JCHArrayUtils.has_row eqs c then
		      begin
			let (eq_err, ineq_err) = Option.get res_opt in
			pr__debug [
                            STR "FOUND check_constraint problem with eqs: ";
                            pp_array_big_int c; STR " ";
			    INT (Array.length eqs + Array.length ineqs); NL;
			    pp_matrix_big_int eqs; NL; STR "     result: "; NL;
			    pp_matrix_big_int eq_err; NL;
			    pp_matrix_big_int ineq_err; NL];
			JCHArrayUtils.implies_constraint_error eqs ineqs c is_eq
		      end
		    else if not is_eq && JCHArrayUtils.has_row ineqs c then
		      begin
			let (eq_err, ineq_err) = Option.get res_opt in
			pr__debug [
                            STR "FOUND check_constraint problem with ineqs: ";
                            pp_array_big_int c; STR " ";
			    INT (Array.length eqs + Array.length ineqs); NL;
			    pp_matrix_big_int ineqs; NL;
			    STR "     result: "; NL;
                            pp_matrix_big_int eq_err; NL;
                            pp_matrix_big_int ineq_err; NL];
			JCHArrayUtils.implies_constraint_error eqs ineqs c is_eq
		      end;
		    if is_eq then
		      begin
			if fst (JCHArrayUtils.implies_constraint
                                  eqs ineqs c false) then
			  begin
			    new_ineqs := c :: !new_ineqs;
			  end
			else
			  let neg_c = Array.map minus_big_int c in
			  if fst (JCHArrayUtils.implies_constraint
                                    eqs ineqs neg_c false) then
			    begin
			      new_ineqs := neg_c :: !new_ineqs;
			    end
		      end
		  end
		else
		  begin
		    if is_eq then new_eqs := c :: !new_eqs
		    else new_ineqs := c :: !new_ineqs
		  end in
	      Array.iteri (check_constraint true a_aug_eqs a_aug_ineqs) s_aug_eqs;
	      Array.iteri
                (check_constraint false a_aug_eqs a_aug_ineqs) s_aug_ineqs;
	      if params#analysis_level > 1 then
		begin
		  Array.iteri
                    (check_constraint true s_aug_eqs s_aug_ineqs) a_aug_eqs;
		  Array.iteri
                    (check_constraint false s_aug_eqs s_aug_ineqs) a_aug_ineqs;
		end;
	      if !new_eqs = [] && !new_ineqs = [] then self#mk_top
	      else
		let p =
                  self#mk_poly
                    new_poly_inds
                    new_index_map
                    (Array.of_list !new_eqs)
                    (Array.of_list !new_ineqs) in
		p#remove_duplicates#minimize;
	    end

    method narrowing (a: 'a) =
      self#meet a

    (* Reorders the columns of the handle to be consistent with the new order
     * map : old index -> new index *)
    method remap_indices old_ind_to_new_ind =
      if bottom || top then {< >}
      else
	let changed_index_map =
          (* old columns -> new index *)
	  List.map (fun (i, j) -> (i, List.assoc j old_ind_to_new_ind)) index_map in
	let new_poly_inds = List.sort compare (List.map snd changed_index_map) in
        (* new columns -> new index *)
	let new_index_map = self#make_index_map new_poly_inds in
	let get_new_col ind = self#get_column_ new_index_map ind in
	let old_to_new_map =
          (* old column -> new column *)
          List.map (fun (i, j) -> (i, get_new_col j)) changed_index_map in
	let nvars = List.length index_map in
	let new_eq_matrix = remap_m nvars old_to_new_map eq_matrix in
	let new_ineq_matrix = remap_m nvars old_to_new_map ineq_matrix in
	{< poly_inds = new_poly_inds;
           index_map = new_index_map;
           eq_matrix = new_eq_matrix;
           ineq_matrix = new_ineq_matrix;
           poly_ind = get_poly_index()
        >}


    (* row.(c) <> 0 *)
    method private combine_eq m row c =
      let lv1 = row.(c) in
      let is_pos = gt_big_int lv1 zero_big_int in
      let combine_row coeff = not (eq_big_int coeff zero_big_int) in
      let new_m = JCHArrayUtils.copy_m m in
      let ncols = Array.length row in
      begin
        for i = 0 to pred (Array.length m) do
	  let lv2 = m.(i).(c) in
	  if combine_row lv2 then
	    for j = 0 to pred ncols do
	      if is_pos then
                new_m.(i).(j) <-
                  sub_big_int
                    (mult_big_int lv1 m.(i).(j)) (mult_big_int lv2 row.(j))
	      else
                new_m.(i).(j) <-
                  sub_big_int
                    (mult_big_int lv2 row.(j)) (mult_big_int lv1 m.(i).(j));
	    done;
        done;
        new_m
      end

    method private project_out_col_eq m c =
      let rows = ref [] in
      let rec proj m' =
	let nrows = Array.length m' in
	if nrows = 0 then
          (!rows, m')
	else
	  begin
	  let r = ref 0 in
	  while !r < nrows && eq_big_int m'.(!r).(c) zero_big_int do
	    incr r
	  done;
	  if !r = nrows then
            (!rows, m')
	  else
	    let row = m'.(!r) in
	    rows := row :: !rows;
	    let new_m = self#combine_eq m' row c in
	    let small_m = JCHArrayUtils.remove_row_m new_m !r in
	    proj small_m
	  end in
      proj m

    (* row.(c) <> 0 *)
    method private combine_ineq m row c =
      let lv1 = row.(c) in
      let is_pos = gt_big_int lv1 zero_big_int in
      let combine_row coeff =
	if eq_big_int coeff zero_big_int then
          false
	else
          (is_pos && lt_big_int coeff zero_big_int)
          || ((not is_pos) && gt_big_int coeff zero_big_int) in
      let ncols = Array.length row in
      let new_rows : big_int array list ref = ref [] in
      for i = 0 to pred (Array.length m) do
	let r = m.(i) in
	let lv2 = r.(c) in
	  if combine_row lv2 then
	    begin
	      let new_row = Array.make ncols zero_big_int in
              let non_zero_coeffs = ref 0 in
	      try
		for j = 0 to pred ncols do
		  let new_coeff =
		    if is_pos then
                      sub_big_int
                        (mult_big_int lv1 r.(j)) (mult_big_int lv2 row.(j))
		    else
                      sub_big_int
                        (mult_big_int lv2 row.(j)) (mult_big_int lv1 r.(j)) in
                  if not (eq_big_int new_coeff zero_big_int) then
                    incr non_zero_coeffs;
		  if (lt_big_int new_coeff params#max_poly_coefficient)
                     || j = pred ncols then
		    new_row.(j) <- new_coeff
		  else
                    raise Exit
		done;
                if !non_zero_coeffs > 2
                   && ge_big_int
                        new_row.(pred ncols) params#max_poly_coefficient then
                  raise Exit;
		new_rows := r :: new_row :: !new_rows;
	      with _ -> new_rows := r :: !new_rows
	    end
	  else
	    begin
	      new_rows := r :: !new_rows;
	    end
      done;
      JCHArrayUtils.remove_trivial_rows (Array.of_list !new_rows)

    method private project_out_col_ineq m c =
      let rec proj m' =
	let nrows = Array.length m' in
	if nrows = 0 then m'
	else
	  begin
	  let r = ref 0 in
	  while !r < nrows && eq_big_int m'.(!r).(c) zero_big_int do
	    incr r
	  done;
	  if !r = nrows then m'
	  else
	    let row = m'.(!r) in
	    let new_m' =
              self#combine_ineq (JCHArrayUtils.remove_row_m m' !r) row c in
	    proj new_m'
	  end in
      proj m

    method private project_out_col (a: 'a) (c: int) =
      let eq_m = a#get_eq_matrix in
      let ineq_m = a#get_ineq_matrix in
      let apoly_dim = List.length a#get_index_map in
      let mk_poly eqs ineqs =
	let constrs =
          (linear_constraints_of_matrix true eqs)
          @ (linear_constraints_of_matrix false ineqs) in
	let constrs' = List.sort_uniq (fun c1 c2 -> c1#compare c2) constrs in
	let (eqs', ineqs') = linear_constraints_to_matrices apoly_dim constrs' in
	self#mk_poly a#get_poly_inds a#get_index_map eqs' ineqs' in
      match self#project_out_col_eq eq_m c with
      |	(r :: _rs, new_eq_m) ->
          let new_ineq_m = self#combine_eq ineq_m r c in
	  mk_poly new_eq_m new_ineq_m
      |	(_, new_eq_m) ->
	  let new_ineq_m = self#project_out_col_ineq ineq_m c in
	  mk_poly new_eq_m new_ineq_m

    (* Projects out indices inds and removes them  *)
    method project_out inds =
      if bottom then self#mk_bottom
      else if top then self#mk_top
      else
	let add_used_col cs_to_remove (i, j) =
	  if List.mem j inds then i :: cs_to_remove
	  else cs_to_remove in
	let cs_to_remove = List.fold_left add_used_col [] index_map in
	if cs_to_remove = [] then {< >}
	else
	  begin
	    let cs_to_remove = List.sort (fun i j -> compare j i) cs_to_remove in
	    let old_dim = List.length poly_inds in
	    let new_dim = old_dim - (List.length cs_to_remove) in
	    let permutation = Array.make old_dim 0 in (* old col -> new col *)
	    let old_col_to_new_col = ref [] in
	    let rec add_col new_index_map new_col extra_col old_col ind =
	      let largest_ind = snd (List.hd (List.rev index_map)) in
	      if ind > largest_ind then new_index_map
	      else if List.mem ind inds then (* has to be projected out*)
		begin
		  if List.mem ind poly_inds then (* has to be removed *)
		    begin
		      permutation.(old_col) <- extra_col;
		      old_col_to_new_col :=
                        (old_col, extra_col) :: !old_col_to_new_col;
		      add_col
                        new_index_map
                        new_col (succ extra_col) (succ old_col) (succ ind)
		    end
		  else (* continue *)
		    begin
		      add_col new_index_map new_col extra_col old_col (succ ind)
		    end
		end
	      else (* does not have to be removed *)
		begin
		  if List.mem ind poly_inds then
		    begin
		      permutation.(old_col) <- new_col;
		      old_col_to_new_col :=
                        (old_col, new_col) :: !old_col_to_new_col;
		      add_col
                        ((new_col, List.assoc old_col index_map) :: new_index_map)
			(succ new_col) extra_col (succ old_col) (succ ind)
		    end
		  else
		    begin
		      add_col new_index_map new_col extra_col old_col (succ ind)
		    end
		end in
	    let new_index_map = List.rev (add_col [] 0 new_dim 0 0) in
	    let new_poly_inds = List.map snd new_index_map in
	    let proj_poly =
              List.fold_left self#project_out_col self cs_to_remove in
	    let new_eq_m =
              remap_m old_dim !old_col_to_new_col proj_poly#get_eq_matrix in
	    let new_ineq_m =
              remap_m old_dim !old_col_to_new_col proj_poly#get_ineq_matrix in
	    let number_cols_removed = List.length cs_to_remove in
	    let reduced_eq_m =
              remove_last_cols_m number_cols_removed new_eq_m in
	    let reduced_ineq_m =
              remove_last_cols_m number_cols_removed new_ineq_m in
	    self#minimize_
              new_poly_inds new_index_map reduced_eq_m reduced_ineq_m
	  end

    (* Projects out the inds and then removes those inds by remapping *)
    method project_out_and_remove inds =
      if bottom || top then {< >}
      else
	begin
	  let poly = self#remove_trivial_ineqs in
	  if poly#is_bottom || poly#is_top then
            poly
	  else
	    begin
	      let largest_ind = snd (List.hd (List.rev poly#get_index_map)) in
	      let rec add_to_map (old_ind, new_ind, map) =
		if old_ind > largest_ind then
                  map
		else if List.mem old_ind inds then
                  add_to_map (old_ind+1, new_ind, map)
		else
                  add_to_map (old_ind+1, new_ind+1, (old_ind, new_ind) :: map) in
	      let old_to_new_ind = add_to_map (0,0,[]) in
	      (poly#project_out inds)#remap_indices old_to_new_ind
	    end
	end

    method add_constraints (constrs: linear_constraint_t list) =
      if constrs = [] || bottom then {< >}
      else
	begin
	  let constr_used_inds = self#get_used_indices_in_constrs constrs in
	  let (new_poly_inds, new_index_map, big_poly) =
	    if top then
	      begin
		let new_index_map = self#make_index_map constr_used_inds in
		(constr_used_inds,
                 new_index_map,
                 self#mk_top_large constr_used_inds new_index_map)
	      end
	    else
	      begin
		let common_inds =
                  self#find_common_inds poly_inds constr_used_inds in
		let new_index_map = self#make_index_map common_inds in
		let s_aug = self#augment common_inds new_index_map self in
		(common_inds, new_index_map, s_aug)
	      end in
	  let new_constrs =
	    let rev_map = List.map (fun (i,j) -> (j,i)) new_index_map in
	    List.map (fun c -> c#remap rev_map) constrs in
	  let new_nvars = List.length new_poly_inds in
	  let (eq_m, ineq_m) =
            linear_constraints_to_matrices new_nvars new_constrs in
	  let new_eq_m = Array.append big_poly#get_eq_matrix eq_m in
	  let new_ineq_m = Array.append big_poly#get_ineq_matrix ineq_m in
	  (self#mk_poly
             new_poly_inds new_index_map new_eq_m new_ineq_m)#remove_duplicates
	end

    method remove_duplicates =
      let constrs =
        List.sort_uniq (fun c1 c2 -> c1#compare c2) self#get_constraints in
      self#mk_poly_from_constraints false constrs

    method add_constrs_from_interval col (interval:interval_t) =
      if bottom || interval#isTop then
        {< >}
      else if interval#isBottom then
        self#mk_bottom
      else
	let constrs = mk_constraints_from_interval true col interval in
	self#add_constraints constrs

    (* constrs should not be an empty list here *)
    method mk_poly_from_constraints minimize constrs =
      let new_poly_inds = self#get_used_indices_in_constrs constrs in
      let new_index_map = self#make_index_map new_poly_inds in
      let new_poly_dim = List.length new_index_map in
      let new_constrs =
	let rev_map = List.map (fun (i,j) -> (j,i)) new_index_map in
	List.map (fun c -> c#remap rev_map) constrs in
      let (eq_m, ineq_m) =
        linear_constraints_to_matrices new_poly_dim new_constrs in
      if minimize then
        self#minimize_ new_poly_inds new_index_map eq_m ineq_m
      else
        {< bottom = false;
           top = false;
           poly_inds = new_poly_inds;
           index_map = new_index_map;
	   eq_matrix = eq_m;
           ineq_matrix = ineq_m;
	   poly_ind = get_poly_index() >}

    method affine_image ind coeff pairs const (interval: CHIntervals.interval_t) =
      if bottom then {< >}
      else
	let used_inds = List.sort compare (List.map fst pairs) in
	if List.mem ind used_inds then
          (* This can only be the loop counter increment *)
	  begin
	    if top then
              self#mk_top
	    else
	      match pairs with
	      | [(_, _)] ->
		 let new_poly_inds =
                   self#find_common_inds
                     poly_inds (self#find_common_inds [ind] used_inds) in
		 let new_index_map = self#make_index_map new_poly_inds in
		 let new_nvars = List.length new_index_map in
		 let s_aug = self#augment new_poly_inds new_index_map self in
		 let new_col = self#get_column_ new_index_map ind in
		 let eq_nrows = Array.length s_aug#get_eq_matrix in
		 let new_eq_matrix = Array.copy s_aug#get_eq_matrix in
		 let ineq_nrows = Array.length s_aug#get_ineq_matrix in
		 let new_ineq_matrix = Array.copy s_aug#get_ineq_matrix in
		 let increment_a a  =
		   let c = a.(new_col) in
		   if not (eq_big_int coeff zero_big_int) then
		     a.(new_nvars) <-
                       sub_big_int a.(new_nvars) (mult_big_int c const) in
		 for i = 0 to pred eq_nrows do
		   increment_a new_eq_matrix.(i)
		 done;
		 for i = 0 to pred ineq_nrows do
		   increment_a new_ineq_matrix.(i)
		 done;
		 self#minimize_
                   new_poly_inds new_index_map new_eq_matrix new_ineq_matrix
	      | _ ->
		 raise (JCHAnalysisUtils.numeric_params#analysis_failed
                          2 "affine_image expected pairs = [(ind,coeff)]")
	  end
	else
	  begin
	    let red_poly =
	      if top then
                {< >}
	      else
		let interval_constraints =
                  mk_constraints_from_interval true ind interval in
		let big_poly = self#add_constraints interval_constraints in
		big_poly#project_out [ind] in
	    let all_pairs = (ind, minus_big_int coeff) :: pairs in
	    let constr = new linear_constraint_t true all_pairs const in
	    red_poly#add_constraints [constr]
	  end

    (* var = var + const *)
    method affine_increment ind const =
      if bottom || top then
        {< >}
      else if self#is_in_poly ind then
	let c = self#get_column ind in
	{< eq_matrix = increment_m eq_matrix c const;
           ineq_matrix = increment_m ineq_matrix c const;
           poly_ind = get_poly_index()
        >}
      else
        {< >}


    (* We can do better for the loop increment case *)
    method affine_preimage
             (ind:int)
             (_coeff: big_int)
             (_pairs: (int * big_int) list)
             (_const: big_int) =
      self#project_out [ind]

    (* copies all the constraints on col1 to col2 as well *)
    method copy_other_col_constrs ind1 ind2 =
      if bottom || top then
        {< >}
      else if List.exists (fun (_,j) -> j = ind1) index_map then
	let new_poly_inds = List.sort compare (ind2 :: (List.map snd index_map)) in
	let new_index_map = self#make_index_map new_poly_inds in
	let s_aug = self#augment new_poly_inds new_index_map self in
	let new_col1 = self#get_column_ new_index_map ind1 in
	let new_col2 = self#get_column_ new_index_map ind2 in
	let copy_col_m m =
	  let new_m = Array.copy m in
	  let copy_col_a a = a.(new_col2) <- a.(new_col1) in
	  for i = 0 to pred (Array.length new_m) do
	    copy_col_a new_m.(i)
	  done;
	  new_m in
	let new_eq_m = copy_col_m s_aug#get_eq_matrix in
	let new_ineq_m = copy_col_m s_aug#get_ineq_matrix in
	self#mk_poly_ new_poly_inds new_index_map new_eq_m new_ineq_m
      else {< >}

    method get_interval ind =
      if bottom then
        bottomInterval
      else if top then
        topInterval
      else if List.mem ind poly_inds then
	begin
	  let other_inds = List.filter (fun i -> i <> ind) poly_inds in
	  let red_poly = self#project_out other_inds in
	  let red_eq_m = red_poly#get_eq_matrix in
	  let red_ineq_m = red_poly#get_ineq_matrix in
	  let interval = ref CHIntervals.topInterval in
	  let add_constr is_eq a =
	    let coeff = a.(0) in
	    let const = a.(1) in
	    if eq_big_int coeff zero_big_int then ()
	    else
	      begin
		let c =
                  mkNumerical_big (minus_big_int (div_big_int const coeff)) in
		let c_int =
		  if is_eq then
                    mkSingletonInterval c
		  else if gt_big_int coeff zero_big_int then
                    new interval_t (bound_of_num c) plus_inf_bound
		  else
                    new interval_t minus_inf_bound (bound_of_num c) in
		interval := !interval#meet c_int
	      end in
	  for i = 0 to pred (Array.length red_eq_m) do
	    add_constr true red_eq_m.(i)
	  done;
	  for i = 0 to pred (Array.length red_ineq_m) do
	    add_constr false red_ineq_m.(i)
	  done;
	  !interval
	end
      else CHIntervals.topInterval

    (* v = x * y and s = m / y
     * Adds v <= m or v >= m if y is positive or negative and
     * there is a relationship between x and s *)
    method add_mult_constr v_ind x_ind s_ind m_ind_opt const_opt y_pos =
      if bottom || top then {< >}
      else
	begin
	  let mk_var_geq_var ind1 ind2 =
            new linear_constraint_t
                false
                [(ind1, unit_big_int); (ind2, minus_big_int unit_big_int)]
                zero_big_int in
	  let mk_var_geq_const ind const =
            new linear_constraint_t
                false [(ind, unit_big_int)] (minus_big_int const) in
	  let mk_const_geq_var ind const =
            new linear_constraint_t
                false [(ind, minus_big_int unit_big_int)] const in
	  let x_geq_s : 'a =
            self#mk_poly_from_constraints false [mk_var_geq_var x_ind s_ind] in
	  let s_geq_x : 'a =
            self#mk_poly_from_constraints false [mk_var_geq_var s_ind x_ind] in
	  let add_leq ind1_opt ind2_opt const_opt =
	    let constrs =
	      match (ind1_opt, ind2_opt, const_opt) with
	      |	(Some ind1, Some ind2, _) -> [mk_var_geq_var ind2 ind1]
	      |	(Some ind1, None, Some const) -> [mk_const_geq_var ind1 const]
	      |	(None, Some ind2, Some const) -> [mk_var_geq_const ind2 const]
	      |	_ -> [] in
	    self#add_constraints constrs in
	  if y_pos then
	    if self#is_included_in self s_geq_x then
	      add_leq (Some v_ind) m_ind_opt const_opt
	    else if self#is_included_in self x_geq_s then
	      add_leq m_ind_opt (Some v_ind) const_opt
	    else {< >}
	  else
	    if self#is_included_in self s_geq_x then
	      add_leq m_ind_opt (Some v_ind) const_opt
	    else if self#is_included_in self x_geq_s then
	      add_leq (Some v_ind) m_ind_opt const_opt
	    else {< >}
	end

    method get_pair_combinations =
      if self#is_top || self#is_bottom then []
      else
	begin
	  let dim = List.length index_map in
	  let all_constraints = ref [] in
	  for i = 0 to pred dim do
	    let proj_poly = self#project_out [i] in
	    if not proj_poly#is_top then
	      all_constraints := !all_constraints @ proj_poly#get_constraints
	  done;
	  !all_constraints
	end

    method to_string =
      if bottom then
	"_|_"
      else if top then
	"T "
        ^ (String.concat
             "\n" (List.map (fun c -> c#to_string) self#get_constraints))
      else
	String.concat "\n" (List.map (fun c -> c#to_string) self#get_constraints)

    method toPretty =
      if bottom then STR "_|_"
      else if top then
	LBLOCK [STR "T ";
		STR "dim: ";  INT (self#get_poly_dim); NL;
		STR "poly_inds: "; pp_list_int poly_inds; NL;
		STR "index_map: "; pp_assoc_list_ints index_map; NL;
		STR "eq_matrix: "; pp_matrix_big_int eq_matrix; NL;
		STR "ineq_matrix: "; pp_matrix_big_int ineq_matrix; NL]
      else
        LBLOCK [INT poly_ind; STR " dim: ";  INT (self#get_poly_dim); NL;
		STR "poly_inds: "; pp_list_int poly_inds; NL;
		STR "index_map: "; pp_assoc_list_ints index_map; NL;
		STR "eq_matrix: "; pp_matrix_big_int eq_matrix; NL;
		STR "ineq_matrix: "; pp_matrix_big_int ineq_matrix; NL]


    method private get_used_in_list ls =
      let rec add_to_list (res, ind) (map, ls) =
	match (map, ls) with
	| ((_, j) :: rest_map, l :: rest_ls) ->
	    if j = ind then add_to_list (l :: res, ind+1) (rest_map, rest_ls)
	    else add_to_list (res, ind + 1)  (map, rest_ls)
	| _ -> List.rev res in
      add_to_list ([], 0) (index_map, ls)


    method restrict_number_constraints =
      if bottom || top then
        ({< >}, false)
      else
	begin
	  let constrs = self#get_constraints in
	  let constrs = List.sort_uniq (fun c1 c2 -> c1#compare c2) constrs in
	  let removed = ref false in
	  let max_constr_pairs =
            List.map (fun c -> (c#get_max_and_nr_coeffs, c)) constrs in
	  let ordered_constrs =
	      let is_larger_constr ((m1,n1),c1) ((m2,n2),c2) =
		match (c1#is_equality, c2#is_equality) with
		| (true, false) -> -1
		| (false, true) -> 1
		| _ ->
		    if eq_big_int m1 m2 then n1 - n2
		    else if gt_big_int m1 m2 then 1
		    else (-1) in
	      List.sort is_larger_constr max_constr_pairs in
	  let rec add_to_list (n, res) constrs =
	    match constrs with
	    | ((max, nr), constr) :: rest_constrs ->
		let is_good constr =
		  constr#is_equality
		  || n < params#max_number_constraints_allowed
                     && lt_big_int max params#max_poly_coefficient
                     && nr <= params#max_number_vars_in_constraint_allowed in
		if is_good constr then
		  add_to_list (n+1, constr :: res) rest_constrs
		else
		  begin
		    removed := true;
		    res
		  end
	    | _ -> res in
	  let new_constrs = add_to_list (0, []) ordered_constrs in
	  if !removed then
	    if new_constrs = [] then
              (self#mk_top, true)
	    else
              (self#mk_poly_from_constraints false new_constrs, true)
	  else
            ({< >}, false)
	end


    method restrict_number_vars =
      if bottom || top then ({< >}, false)
      else
	begin
	  let removed = ref false in
	  let good_constrs = new ConstraintCollections.set_t in
	  let inds_in_bad_constrs = new CHUtils.IntCollections.set_t in
	  let add_constr is_self (p: 'a) =
	    let constrs = p#get_constraints in
	    let max_constr_pairs =
              List.map (fun c -> (c#get_max_and_nr_coeffs, c)) constrs in
	    let add_to_list
                  (((_max, nr), constr):(big_int * int) * linear_constraint_t) =
	      if constr#is_const then
                ()
	      else if nr <= params#max_number_vars_in_constraint_allowed then
		good_constrs#add constr
	      else if is_self then
		let (pairs, _) = constr#get_pairs_const in
                begin
		  inds_in_bad_constrs#addList (List.map fst pairs);
		  removed := true
		end in
	    List.iter add_to_list max_constr_pairs in
	  add_constr true self;
	  let proj_ind ind = add_constr false (self#project_out [ind]) in
	  inds_in_bad_constrs#iter proj_ind;

	  let reduced_constrs = new ConstraintCollections.set_t in
	  let remove_redundant_ineqs c =
	    if c#is_equality then
              reduced_constrs#add c
	    else
	      begin
		let (pairs, const) = c#get_pairs_const in
		let eq = new linear_constraint_t true pairs const in
		if not (good_constrs#has eq) then reduced_constrs#add c
	      end in
	  good_constrs#iter remove_redundant_ineqs;
	  if !removed then
	    if reduced_constrs#isEmpty then
              (self#mk_top, true)
	    else
              (self#mk_poly_from_constraints false reduced_constrs#toList, true)
	  else
            (self#mk_poly_from_constraints false reduced_constrs#toList, false)
	end

    method to_pretty vars =
      if bottom then
	STR "_|_"
      else if top then
	let vars_a = Array.of_list vars in
	LBLOCK [STR "T ";
		 STR "dim: ";  INT (self#get_poly_dim); NL;
		 STR "poly_inds: "; pp_list_int poly_inds; NL;
		 STR "index_map: "; pp_assoc_list_ints index_map; NL;
		 pretty_print_list
                   self#get_constraints
                   (fun c -> LBLOCK [c#to_pretty vars_a; NL]) "" "" ""]

      else
	let vars_a = Array.of_list vars in
	LBLOCK [INT poly_ind; STR " dim: ";  INT (self#get_poly_dim); NL;
		 STR "poly_inds: "; pp_list_int poly_inds; NL;
		 STR "index_map: "; pp_assoc_list_ints index_map; NL;
		 pretty_print_list
                   self#get_constraints
                   (fun c -> LBLOCK [c#to_pretty vars_a; NL]) "" "" ""]

  end

let top_poly = new poly_t

let top_poly_large poly_inds =
  let sorted_inds = List.sort compare poly_inds in
  let add_index_to_map (i, res) ind = (i + 1, (i, ind) :: res) in
  let (_, map) = List.fold_left add_index_to_map (0, []) sorted_inds in
  let index_map = List.rev map in
  (new poly_t)#mk_top_large sorted_inds index_map

let bottom_poly = (new poly_t)#mk_bottom

let mk_poly_from_constraints minimize (constrs: linear_constraint_t list) =
  if constrs = [] then
    (new poly_t)
  else
    (new poly_t)#mk_poly_from_constraints minimize constrs

(* move simple ineqs from the poly into the interval array.
 * Also eliminate variables that are constant from the poly *)
let move_simple_ineqs_to_intervals
      (poly: poly_t) (interval_array:JCHIntervalArray.interval_array_t) =
  if poly#is_top || poly#is_bottom then
    (poly, interval_array)
  else
    begin
      let const_vars = interval_array#get_singletons in
      let constrs =
	List.map
          (fun constr -> constr#replace_consts const_vars) poly#get_constraints in
      let restr_array = interval_array#copy in
      let meet_interval (i: int) (interval: CHIntervals.interval_t) =
	let int = restr_array#get i in
	if int#isBottom then
	  begin
	    restr_array#set i (interval#meet (restr_array#get_type_interval i));
	    None
	  end
	else
	  begin
	    let new_interval = int#meet interval in
	    restr_array#set i new_interval;
	    match (int#singleton, new_interval#singleton) with
	    |	(None, Some n) -> Some (i, n#getNum)
	    |	_ -> None
	  end in
      let rec move_constr
                (non_interval_constrs:linear_constraint_t list)
                (not_seen_constrs: linear_constraint_t list) =
	match not_seen_constrs with
	| constr :: rest_not_seen_constrs ->
	   if constr#get_used_indices = [] then
             move_constr non_interval_constrs rest_not_seen_constrs
	    else
	      begin
		match constr#get_v_interval with
		| Some (c, interval) ->
		    begin
		      match meet_interval c interval with
		      |	Some pair ->
			 let new_constrs =
                           non_interval_constrs @ rest_not_seen_constrs in
			 let new_constrs =
                           List.map
                             (fun constr ->
                               constr#replace_consts [pair]) new_constrs in
			  move_constr [] new_constrs
		      |	_ ->
                         move_constr non_interval_constrs rest_not_seen_constrs
		    end
		| _ ->
		   move_constr
                     (constr :: non_interval_constrs) rest_not_seen_constrs
	      end
	| [] -> non_interval_constrs in
      let restr_constrs = move_constr [] constrs in
      let restr_poly =
	match restr_constrs with
	| [] -> top_poly
	| _ -> mk_poly_from_constraints false restr_constrs in
      (restr_poly, restr_array)
    end

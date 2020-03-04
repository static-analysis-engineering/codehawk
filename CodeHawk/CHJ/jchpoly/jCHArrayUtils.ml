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
open CHCommon
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil

(* jchsys *)
open JCHPrintUtils

let dbg = ref false 

let find_gcd (m:big_int) (n:big_int) = 
  let gcd = ref unit_big_int in
  let rec find_gcd_rec mn mx = (* mn <= mx *)
    if eq_big_int mn zero_big_int then 
      abs_big_int !gcd 
    else
      begin
        gcd := mn ;
        find_gcd_rec (mod_big_int mx mn) mn
      end in
  if eq_big_int m n then 
    abs_big_int m
  else if lt_big_int m n then
    find_gcd_rec m n 
  else 
    find_gcd_rec n m;;

let rec find_first_non_zero_a (a: big_int array) = 
  let iopt = ref None in
  try
    for i = 0 to pred (Array.length a) do
      if not (eq_big_int a.(i) zero_big_int) then
        begin
	  iopt := Some i;
	  raise Exit
        end
    done ;
    !iopt
  with
  | Exit -> !iopt

let rec find_abs_min_non_zero_a (a:big_int array) = 
  match find_first_non_zero_a a with 
  | Some i -> 
     let min_i = ref i and
	 min_ai = ref (abs_big_int a.(i)) in
     for i = 0 to pred (Array.length a) do
       if not (eq_big_int a.(i) zero_big_int)
          && (lt_big_int (abs_big_int a.(i)) !min_ai) then
         begin
	   min_i := i ;
	   min_ai := abs_big_int a.(i)
	 end
     done ;
     Some (!min_i, !min_ai)
  | None -> None

let for_all_ind_a p a first_index last_index = 
  try 
    for i = first_index to last_index do
      if not (p i a.(i)) then 
	raise Exit
    done ;
    true
  with Exit -> false

let for_all_a p a = 
  for_all_ind_a p a 0 (pred (Array.length a))

let exists_a p a = 
  try 
    for i = 0 to pred (Array.length a) do
      if p i a.(i) then 
	raise Exit
    done ;
    false
  with Exit -> true

let equal_a a1 a2 = 
  for_all_a 
    (fun i ai -> eq_big_int ai a2.(i)) 
    a1


let find_gcd_a (a: big_int array) = 
  let rec find_gcd_rec (array: big_int array) = 
    match find_abs_min_non_zero_a array with
    | Some (min_i, min_vl) -> 
       if for_all_a (fun j aj ->
              j = min_i || eq_big_int aj zero_big_int) array then 
	  min_vl
	else 
	  let takeMod i ai = 
	    if i = min_i then 
	      ai 
	    else 
	      mod_big_int ai min_vl in
	  let newa = Array.mapi takeMod array in
	  find_gcd_rec newa 
    | None -> unit_big_int in
  find_gcd_rec a

let find_mult_a a = 
  let res = ref unit_big_int in
  for i = 0 to pred (Array.length a) do
    res := mult_big_int !res a.(i)
  done ;
  !res

let find_lcm_a a = 
  div_big_int (find_mult_a a) (find_gcd_a a)
      
let normalize_a a =
  let len = Array.length a in      
  let gcd = find_gcd_a a in
  if gt_big_int gcd unit_big_int then 
    begin
      for i = 0 to pred len do
	a.(i) <- div_big_int a.(i) gcd
      done
    end

(* linear combination of a1 and a2 such that r[i] = 0 *)
let combine a1 a2 i = 
  let len = Array.length a1 in
  let r = Array.make len zero_big_int in
  let gcd = find_gcd a1.(i) a2.(i) in
  let m1 = div_big_int a1.(i) gcd in
  let m2 = div_big_int a2.(i) gcd in
  begin
    for i = 0 to pred len do 
      r.(i) <- sub_big_int (mult_big_int m2 a1.(i)) (mult_big_int m1 a2.(i))
    done ;
    normalize_a r ;
    r
  end

let normalize_pos_a a = 
  let len = Array.length a in      
  let gcd = find_gcd_a a in
  if gt_big_int gcd unit_big_int then 
    begin
      let divisor = ref zero_big_int in
      for i = 0 to pred len do
	if not (eq_big_int a.(i) zero_big_int) then
	  begin
	    if eq_big_int !divisor zero_big_int then 
	      divisor := if gt_big_int a.(i) zero_big_int then gcd else minus_big_int gcd ;
	    a.(i) <- div_big_int a.(i) !divisor
	  end
      done 
    end
    
let normalize_pos_m m  = 
  let  nrows = Array.length m in
  for r = 0 to pred nrows do
    normalize_pos_a m.(r)
  done

let copy_m m = 
  let nrows = Array.length m in
  if nrows = 0 then 
    Array.copy m
  else
    let ncols = Array.length m.(0) in
    let mc = Array.make_matrix nrows ncols zero_big_int in
    begin
      for i = 0 to pred nrows do
        mc.(i) <- Array.copy m.(i) 
      done ;
      mc
    end

let swap_rows_m m i j =
  let tmp = m.(i) in
  begin
    m.(i) <- m.(j);
    m.(j) <- tmp
  end
  
(* for a reduced triangular matrix *)
let remove_0_rows_m m = 
  let nrows = Array.length m in
  let ncols = Array.length m.(0) in
  let new_nrows = ref (pred nrows) in
  begin 
    try 
      for i = pred nrows downto 0 do 
	for j = 0 to pred ncols do
	  if not (eq_big_int m.(i).(j) zero_big_int) then begin
	    new_nrows := succ i ;
	    raise Exit 
	  end
	done 
      done
    with Exit -> () 
  end ;
  if !new_nrows = nrows then
    m
  else 
    Array.sub m 0 !new_nrows

let equal_m m1 m2 = 
  match (Array.length m1, Array.length m2) with 
  | (0, 0) -> true
  | (nrows1, nrows2) -> 
      try 
	if nrows1 = nrows2 then 
	  let ncols1 = Array.length m1.(0) in
	  if ncols1 = Array.length m2.(0) then begin
	    for i = 0 to pred nrows1 do 
	      for j = 0 to pred ncols1 do
		if not (eq_big_int m1.(i).(j) m2.(i).(j)) then
		  raise Exit 
	      done
	    done ;
	    true
	  end
	  else false 
	else false
      with Exit -> false

(* Assumes reduced triangular form
 * Assumes matrix is not empty and has solutions
 * In the case of join, cols_used should have the cols used by both *)
let find_indep_sols_m m sol_size cols_used  = 
  let ncols = Array.length m.(0) in
  let last_c = pred ncols in
  let last_coeff = pred last_c in
  let nums = Array.make_matrix sol_size last_c zero_big_int in
  let dens = Array.make_matrix sol_size last_c unit_big_int in
  let setNewVals r c i = 
    let a = m.(r) in
    let solnums = nums.(i) in
    let soldens = dens.(i) in
    let cden =
      let mlt = ref unit_big_int in
      for j = succ c to last_coeff do
	mlt := mult_big_int !mlt soldens.(j)
      done ;
      !mlt in
    let res = 
      let rs = ref zero_big_int in
      for j = succ c to last_coeff do
	rs := add_big_int !rs (mult_big_int (mult_big_int a.(j) (div_big_int cden soldens.(j))) solnums.(j))
      done ;
      !rs in
    let solden = mult_big_int a.(c) cden in
    let solnum = minus_big_int (add_big_int (mult_big_int a.(last_c) cden) res) in 
    let gcd = find_gcd solden solnum in
    let div = if gt_big_int solden zero_big_int then gcd else minus_big_int gcd in
    if not (eq_big_int solnum zero_big_int) then 
      begin
	solnums.(c) <- div_big_int solnum div;
	soldens.(c) <- div_big_int solden div 
      end in
  (* set the 'free' vars *)
  let r = ref 0 in
  for j = 0 to last_coeff do 
    if cols_used.(j) = -1 then 
      begin
	nums.(!r).(j) <- unit_big_int ;
	incr r 
      end
  done ;
  (* set the lead variables *)
  for j = last_coeff downto 0 do 
    let r = cols_used.(j) in
    if r > -1 then 
      for i = 0 to pred sol_size do
	setNewVals r j i
      done
  done ;
  (nums, dens)

(* Sets -2 if the column is all 0;
 * r if row r has a lead coeff at the column,
 * -1 otherwise *)
let find_cols_used_m m = 
  let nrows = Array.length m in
  let last_c = pred (Array.length m.(0)) in
  let used = Array.make last_c (-2) in
  let ncols_used = ref 0 in
  for i = 0 to pred nrows do 
    let row_all_0 = ref true in
    for j = i to pred last_c do 
      if not (eq_big_int m.(i).(j) zero_big_int) then 
	if !row_all_0 then begin
	  if used.(j) = -2 then 
	    incr ncols_used ;
	  row_all_0 := false ;
	  used.(j) <- i ;
	end
	else if used.(j) = -2 then begin
	  used.(j) <- -1 ;
	  incr ncols_used
	end
    done ;
  done ;
  used

let get_common_col_used_a cols_used1 cols_used2 = 
  let ncols = Array.length cols_used1 in
  let ncols_used = ref 0 in
  for j = 0 to pred ncols do
    match (cols_used1.(j), cols_used2.(j)) with 
    | (-2, -2) -> ()
    | (-2, _) -> 
	cols_used1.(j) <- -1 ;
	incr ncols_used 
    | (_, -2) -> 
	cols_used2.(j) <- -1 ;
	incr ncols_used 
    | _ -> 
	incr ncols_used
  done ;
  if ncols < Array.length cols_used2 && cols_used2.(ncols) <> -2 then 
    incr ncols_used ;
  !ncols_used

let find_eq_from_sol_a (nums, dens) = 
  let size = Array.length nums in
  let lcm = find_lcm_a dens in
  let eq = Array.make (succ size) zero_big_int in
  let first = ref true in
  let slcm = ref unit_big_int in
  for i = 0 to pred size do
    if not (eq_big_int nums.(i) zero_big_int) then begin
      if !first then begin
	first := false ;
	slcm := if gt_big_int nums.(i) zero_big_int then lcm else minus_big_int lcm 
      end ;
      eq.(i) <- mult_big_int nums.(i)  (div_big_int !slcm dens.(i)) 
    end
  done ;
  eq.(size) <- !slcm ;
  eq

let find_eqs_from_sols_m (nums, dens) = 
  let nrows = Array.length nums in 
  let ncols = Array.length nums.(0) in 
  let eqs = Array.make_matrix nrows (succ ncols) zero_big_int in
  for i = 0 to pred nrows do
    eqs.(i) <- find_eq_from_sol_a (nums.(i), dens.(i)) 
  done ;
  eqs

let implies_eq m a = 
  let nrows = Array.length m in
  if nrows = 0 then 
    true 
  else 
    let ncols = Array.length m.(0) in
    let a' = Array.copy a in
    let r = ref 0 in
    try 
      for j = 0 to pred ncols do 
	let lv2 = a'.(j) in
	if not (eq_big_int lv2 zero_big_int) then 
	  while eq_big_int m.(!r).(j) zero_big_int && !r < nrows do
	    incr r;
	  done ;
	  if !r = nrows then 
	    raise Exit
	  else 
	    let lv1 = m.(!r).(j) in
	    for k = 0 to pred ncols do 
	      a'.(k) <- sub_big_int (mult_big_int lv1 a'.(k)) (mult_big_int lv2 m.(!r).(k))
	    done 
      done ;
      true
    with Exit -> 
	false

let exchange_m m i1 i2 = 
  let aux = m.(i1) in
  m.(i1) <- m.(i2) ;
  m.(i2) <- aux 

let max_n_rays = JCHAnalysisUtils.numeric_params#max_number_rays

(* After "A Note on Chernikova's Algorithm" by H. Le Verge 
 * dim is the number of variables = number of columns including 
 * one for constants *)
let chernikova_m
      (bid_rays: big_int array array)
      (uni_rays: big_int array array)
      n_bid_rays
      n_unid_rays
      inequality = 
  let dim = !n_bid_rays in
  let ncols = Array.length bid_rays.(0) in
  let common_zero = Array.make ncols 0 in
  for k = dim to pred ncols do 
  (*  Find a bidirectional ray which does not saturate current constraint *)
    let index_non_zero = ref (-1) in
    (try 
      for i = 0 to pred !n_bid_rays do 
	if not (eq_big_int bid_rays.(i).(k) zero_big_int) then 
	  begin
	    index_non_zero := i ;
	    raise Exit
	  end ;
      done ;
    with Exit -> ()) ;
    if !index_non_zero <> -1 then 
      begin
	(* Discard index_non_zero bidirectional ray *)
	decr n_bid_rays ;
	if !n_bid_rays <> !index_non_zero then 
	  begin
	    let p = bid_rays.(!n_bid_rays) in 
	    bid_rays.(!n_bid_rays) <- bid_rays.(!index_non_zero) ;
	    bid_rays.(!index_non_zero) <- p 
	  end ;
	(* Compute the new linearity space *)
	for i = 0 to pred !n_bid_rays do
	  if not (eq_big_int bid_rays.(i).(k) zero_big_int) then 
	    begin
	      bid_rays.(i) <- combine bid_rays.(i) bid_rays.(!n_bid_rays) k ;
	    end
	done ; 
        (* Add the positive part of index_non_zero bidirectional ray 
         * to the set of unidirectional rays *)
	if !n_unid_rays = max_n_rays then 
	  raise (JCHAnalysisUtils.numeric_params#analysis_failed
                   2 "too many rays");
	if lt_big_int bid_rays.(!n_bid_rays).(k) zero_big_int then 
	  begin
	    for j = 0 to pred ncols do 
	      uni_rays.(!n_unid_rays).(j) <- minus_big_int bid_rays.(!n_bid_rays).(j) ;
	    done
	  end
	else 
	  begin
	    for j = 0 to pred ncols do 
	      uni_rays.(!n_unid_rays).(j) <- bid_rays.(!n_bid_rays).(j) ;
	    done
	  end ;
        (* Compute the new pointed cone *)
	for i = 0 to pred !n_unid_rays do 
	  if not (eq_big_int uni_rays.(i).(k) zero_big_int) then 
	    uni_rays.(i) <- combine uni_rays.(i) uni_rays.(!n_unid_rays) k ;
	done ;
	if inequality.(k) = 1 then incr n_unid_rays ;
      end 
    else 
      begin
	(* Sort rays : 0 <= i < equal_bound : saturates the constraint *)
        (*             equal_bound <= i < sup_bouns : verify he constraint *)
        (*             sup_bound <= i < bound : does not verify *)
	let equal_bound = ref 0 in
	let sup_bound = ref 0 in
	let inf_bound = ref !n_unid_rays in 
	while !inf_bound > !sup_bound do 
	  if eq_big_int uni_rays.(!sup_bound).(k) zero_big_int then 
	    begin
	      exchange_m uni_rays !equal_bound !sup_bound ;
	      incr equal_bound ;
	      incr sup_bound 
	    end
	  else if lt_big_int uni_rays.(!sup_bound).(k) zero_big_int then 
	    begin
	      decr inf_bound ;
	      exchange_m uni_rays !inf_bound !sup_bound ;
	    end
	  else incr sup_bound
	done ;
        (* Computes only the new pointed cone *)
	let bound = ref !n_unid_rays in
	for i = !equal_bound to pred !sup_bound do 
	  for j = !sup_bound to pred !bound do 
            (* Computes the set of common saturated constraints *)
	    let n_common_constraints = ref 0 in
	    for l = dim to pred k do 
	      if eq_big_int uni_rays.(i).(l) zero_big_int && eq_big_int uni_rays.(j).(l) zero_big_int then 
		begin
		  common_zero.(!n_common_constraints) <- l ;
		  incr n_common_constraints 
		end 
	    done ;
	    if (!n_common_constraints + !n_bid_rays >= dim - 2) then 
	      begin
	    (* Check whether a ray m saturates the same set of constraints *)
		let redundant = ref false in
		(try 
		  for m = 0 to pred !bound do 
		    let l = ref 0 in
		    if m <> i && m <> j then 
		      begin
			(try
			  while !l < !n_common_constraints do 
			    if not (eq_big_int uni_rays.(m).(common_zero.(!l)) zero_big_int) then raise Exit ;
			    incr l
			  done 
			with Exit -> ()) ;
			if !l = !n_common_constraints then 
			  begin
		        (* The combination of ray i and j will generate a non-extremal ray *)
			    redundant := true ;
			    raise Exit
			  end ;
		      end
		  done 
		with Exit -> ()) ;
		if not !redundant then 
		  begin
		    if !n_unid_rays = max_n_rays then 
		      begin
			raise (JCHAnalysisUtils.numeric_params#analysis_failed 2 "too many rays")
		      end ;
		     (* Compute the new ray *)
		    uni_rays.(!n_unid_rays) <- combine uni_rays.(j) uni_rays.(i) k ;
		    incr n_unid_rays ;
		  end
	      end 
	  done 
	done ;
        (* Eliminates all non-extremal rays *)
	let j = ref (if inequality.(k) = 1 then !sup_bound else !equal_bound) in
	let i = ref !n_unid_rays in
	while !j < !bound && !i > !bound do
	  decr i ;
	  exchange_m uni_rays !i !j ;
	  incr j
	done ;
	if !j = !bound then n_unid_rays := !i
	else n_unid_rays := !j ;
      end
  done


let find_ineq_sols_m add_1_geq_0 eq_m ineq_m = 
  let eq_nrows = Array.length eq_m in
  let ineq_nrows = Array.length ineq_m in
  let nrows = eq_nrows + ineq_nrows in
  let ncols = 
    if eq_nrows = 0 then Array.length ineq_m.(0) 
    else 
      let nc1 = Array.length eq_m.(0) in
      if ineq_nrows = 0 then nc1
      else if nc1 <> Array.length ineq_m.(0) then 
	begin
	  raise
            (JCHAnalysisUtils.numeric_params#analysis_failed
               2 "programming error: find_ineq_sols_m, eq and ineq have different number of columns")
	end
      else nc1 in
  let dim = ncols in 
  let new_ncols = 
    if add_1_geq_0 then dim + eq_nrows + ineq_nrows + 1 
    else dim + eq_nrows + ineq_nrows in
  let new_m = Array.make_matrix dim new_ncols zero_big_int in

  for i = 0 to pred dim do 
    new_m.(i).(i) <- unit_big_int 
  done ;
  let new_i = ref dim in

  (try 
  for i = 0 to pred eq_nrows do 
    for j = 0 to pred ncols do 
      new_m.(j).(!new_i) <- eq_m.(i).(j) 
    done ;
    incr new_i ;
  done ;
  with Exit -> pr__debug [pp_matrix_big_int new_m; NL; NL] ) ;

  for i = 0 to pred ineq_nrows do 
    for j = 0 to pred ncols do 
      new_m.(j).(!new_i) <- ineq_m.(i).(j) 
    done ;
    incr new_i
  done ;
  let uni_rays = Array.make_matrix max_n_rays new_ncols zero_big_int in
  let inequality = Array.make new_ncols 0 in
  for i = dim + eq_nrows to pred (dim + nrows) do 
    inequality.(i) <- 1 
  done ;
  if add_1_geq_0 then 
    begin
      new_m.(pred dim).(pred new_ncols) <- unit_big_int ;
      inequality.(pred new_ncols) <- 1 ;
    end ;
  let n_bid_rays = ref dim in
  let n_unid_rays = ref 0 in
  chernikova_m new_m uni_rays n_bid_rays n_unid_rays inequality ;
  let restr_bid_rays = Array.make_matrix !n_bid_rays ncols zero_big_int in
  for i = 0 to pred !n_bid_rays do 
    Array.blit new_m.(i) 0 restr_bid_rays.(i) 0 ncols
  done ;
  let restr_uni_rays = Array.make_matrix !n_unid_rays ncols zero_big_int in  
  let has_vertex = ref false in
  for i = 0 to pred !n_unid_rays do 
    Array.blit uni_rays.(i) 0 restr_uni_rays.(i) 0 ncols ;
    if not (eq_big_int uni_rays.(i).(pred ncols) zero_big_int) then has_vertex := true;
  done ;
  (restr_bid_rays, restr_uni_rays, !has_vertex)


let add_row_m m a init_element = 
  let nrows = Array.length m in
  let ncols = Array.length a in
  let new_m = Array.make_matrix (succ nrows) ncols init_element in
  begin
    Array.blit m 0 new_m 0 nrows ;
    new_m.(nrows) <- a ;
    new_m
  end

let add_rows_m m alist init_element = 
  if alist = [] then
    m 
  else
    let nrows = Array.length m in
    let length = List.length alist in
    let ncols = Array.length (List.hd alist) in
    let new_nrows = nrows + length in
    let new_m = Array.make_matrix new_nrows ncols init_element in
    Array.blit m 0 new_m 0 nrows ;
    let i = ref nrows in
    let rec add_rows alist = 
      match alist with 
      | a :: rest_alist -> 
	  new_m.(!i) <- a;
	  incr i ;
	  add_rows rest_alist
      | _ -> () in
    begin
      add_rows alist;
      new_m
    end
    
let remove_row_m m r = 
  let nrows = Array.length m in
  let new_m = Array.make_matrix (pred nrows) (Array.length m.(0)) zero_big_int in
  begin
    Array.blit m 0 new_m 0 r ;
    Array.blit m (succ r) new_m r (nrows - r - 1) ;
    new_m
  end

let remove_rows_m m rs = 
  let number_removed = List.length rs in
  if number_removed = 0 then
    m 
  else if Array.length m = 0 then
    m
  else 
    begin
      let sorted_rs = List.sort compare rs in
      let nrows = Array.length m in
      let ncols = Array.length m.(0) in
      if number_removed = nrows then Array.make_matrix 0 ncols (zero_big_int) 
      else 
	begin
	  let new_m = Array.make_matrix (nrows - number_removed) ncols zero_big_int in
	  let new_i = ref 0 in
	  let removed_rows = ref sorted_rs in
	  let removed_row = ref (List.hd sorted_rs) in
	  for i = 0 to pred nrows do 
	    if i = !removed_row then 
	      begin
		removed_rows := List.tl !removed_rows ;
		match !removed_rows with 
		| r :: _ -> 
		    removed_row := r ;
		| _ -> ()
	      end
	    else 
	      begin
		new_m.(!new_i) <- m.(i) ;
		incr new_i
	      end
	  done ;
	  new_m
	end
    end 

let remove_trivial_rows ineq_m = 
  let nrows = Array.length ineq_m in
  if nrows = 0 then
    ineq_m
  else 
    begin
      let nvars = pred (Array.length ineq_m.(0)) in
      let trivial_rows = ref [] in
      for i = 0 to pred nrows do
	let a = ineq_m.(i) in
	try
	  for j = 0 to pred nvars do 
	    if not (eq_big_int a.(j) zero_big_int) then
              raise Exit 
	  done ;
	  if not (eq_big_int a.(nvars) zero_big_int) then
            trivial_rows := i :: !trivial_rows 
	with Exit -> () 
      done ;
      let reduced_ineq_m = remove_rows_m ineq_m !trivial_rows in
      reduced_ineq_m
    end

let check_for_bottom eq_m ineq_m = 
  let check_eq eq = 
    let nvars = pred (Array.length eq) in
    try
      for j = 0 to pred nvars do
	if not (eq_big_int eq.(j) zero_big_int) then
          raise Exit
      done ;
      eq_big_int eq.(nvars) zero_big_int
    with Exit -> true in
  let check_ineq ineq = 
    let nvars = pred (Array.length ineq) in
    try
      for j = 0 to pred nvars do
	if not (eq_big_int ineq.(j) zero_big_int) then
          raise Exit
      done ;
      ge_big_int ineq.(nvars) zero_big_int
    with Exit -> true in

  try 
    for i = 0 to pred (Array.length eq_m) do 
      if not (check_eq eq_m.(i)) then raise Exit
    done ;
    for i = 0 to pred (Array.length ineq_m) do 
      if not (check_ineq ineq_m.(i)) then raise Exit
    done ;
    true 
  with Exit -> false



let minimize_m eq_m ineq_m = 
  let (eq'_m, ineq'_m, has_vertex) = find_ineq_sols_m true eq_m ineq_m in
  let _ = check_for_bottom eq'_m ineq'_m in
  if Array.length eq'_m = 0 && Array.length ineq'_m = 0 || not has_vertex then
    None 
  else 
    begin
      let (new_eq_m, new_ineq_m, _) = find_ineq_sols_m false eq'_m ineq'_m in
      if check_for_bottom new_eq_m new_ineq_m then 
	begin
      (* remove 1 >= 0 *)
	  let nrows = Array.length new_ineq_m in
	  if nrows = 0 then Some (new_eq_m, new_ineq_m)
	  else 
	    begin
	      let reduced_ineq_m = remove_trivial_rows new_ineq_m in
	      Some (new_eq_m, reduced_ineq_m)
	    end
	end
      else None
    end


let implies_constraint eq_m ineq_m constr is_eq = 
  let implies_eq eq_m ineq_m eq = 
    let const_col = Array.length eq - 1 in
    let const = eq.(const_col) in
    let leq_constr = Array.copy eq in
    leq_constr.(const_col) <- sub_big_int const unit_big_int ;
    let leq_ineq_m = add_row_m ineq_m leq_constr zero_big_int in

    match minimize_m eq_m leq_ineq_m with
    | None -> 
	begin
	  let geq_constr = Array.map minus_big_int eq in
	  geq_constr.(const_col) <- sub_big_int geq_constr.(const_col) unit_big_int ;
	  let geq_ineq_m = add_row_m ineq_m geq_constr zero_big_int in
	  match minimize_m eq_m geq_ineq_m with
	  | None -> (true, None)
	  | Some (eqs, ineqs) -> (false, Some (eqs, ineqs))
	end 
    | Some (eqs, ineqs) -> (false, Some (eqs, ineqs)) in
  
  let implies_ineq eq_m ineq_m ineq =     
    let const_col = Array.length ineq - 1 in
    let opp_constr = Array.map minus_big_int ineq in
    opp_constr.(const_col) <- sub_big_int opp_constr.(const_col) unit_big_int ;
    let new_ineq_m = add_row_m ineq_m opp_constr zero_big_int in
    match minimize_m eq_m new_ineq_m with
    | None -> (true, None)
    | Some (eqs, ineqs)  -> 
	(false, Some (eqs, ineqs)) in
  
  if is_eq then implies_eq eq_m ineq_m constr
  else implies_ineq eq_m ineq_m constr

let implies_constraint_error eq_m ineq_m constr is_eq = 
  let implies_ineq_err eq_m ineq_m ineq = 
    
    let small_ineq_m = ref ineq_m in
    let m = ref ineq_m in
    let n = ref (Array.length !small_ineq_m) in
    
    try 
      while !n > 0 do
	decr n;
	m := Array.make_matrix !n (Array.length ineq) zero_big_int ;
	for i = 0 to !n-1 do 
	  begin
	    if i > 0 then 
	      Array.blit !small_ineq_m 0 !m 0 i ;
	    if i < !n - 1 then
	      Array.blit !small_ineq_m (i + 1) !m i (!n - i) ;
	    if not (fst (implies_constraint eq_m !small_ineq_m ineq false)) then
	      raise Exit
	  end
	done ;
      done
    with Exit ->
      begin
	pr__debug [STR "FOUND smallest n =  "; INT (!n + 1); NL] ;
	pr__debug [STR "m: "; NL; pp_matrix_big_int !m; NL]
      end in
         
  let implies_eq_err eq_m ineq_m eq = 
    implies_ineq_err eq_m ineq_m eq;
    let leq_constr = Array.map minus_big_int eq in
    implies_ineq_err eq_m ineq_m leq_constr in
  
  if is_eq then
    implies_eq_err eq_m ineq_m constr
  else
    implies_ineq_err eq_m ineq_m constr 

let add_col_a a c n = 
  let ncols = Array.length a in
  let new_a = Array.make (succ ncols) n in
  Array.blit a 0 new_a 0 c;
  Array.blit a c new_a (succ c) (ncols - c) ;
  new_a 

let add_col_m m c n = 
  let new_m = Array.copy m in
  for i = 0 to pred (Array.length m) do 
    new_m.(i) <- add_col_a m.(i) c n 
  done ;
  new_m
  
let remove_col_a a c = 
  let ncols = Array.length a in
  let new_a = Array.make (pred ncols) zero_big_int in
  Array.blit a 0 new_a 0 c;
  Array.blit a (succ c) new_a c (ncols - c - 1) ;
  new_a

let remove_col_m m c = 
  let new_m = Array.copy m in
  for i = 0 to pred (Array.length m) do 
    new_m.(i) <- remove_col_a m.(i) c
  done ;
  new_m

(* cs have to be ordered from largest to smallest *)
let remove_cols_m m cs = 
  List.fold_left remove_col_m m cs 

(* It does not look at the constant column *)
let get_used_cols_a a = 
  let used_cols = ref [] in
  for i = 0 to (Array.length a) - 2 do
    if not (eq_big_int a.(i) zero_big_int) then used_cols := i :: !used_cols
  done ;
  !used_cols

let pp_with_vars_m m (vars: variable_t list) (rel: string) : pretty_t = 
  if (Array.length m) = 0 then STR "T"
  else 
    let ncols = Array.length m.(0) in
    let output_list (row: big_int array) (res, i, first)  v = 
      let n = row.(i) in
      if eq_big_int n zero_big_int then 
	(res, succ i, first) 
      else if eq_big_int n unit_big_int then 
	begin
	  if i = pred ncols then 
	    (STR " + 1" :: res, succ i, false)
	  else if first then 
	    (v#toPretty :: res, succ i, false)
	  else 
	    ((LBLOCK [STR " + "; v#toPretty]) :: res, succ i, false)
	end
      else if eq_big_int n (minus_big_int unit_big_int) then 
	begin
	  if i = pred ncols then 
	    (STR " - 1" :: res, succ i, false)
	  else if first then
	    ((LBLOCK [STR "-"; v#toPretty]) :: res, succ i, false)
	  else
	    ((LBLOCK [STR " - ";v#toPretty]) :: res, succ i, false)
	end
      else 
	begin
	  if i = pred ncols then 
	    if gt_big_int n zero_big_int then 
	      ((LBLOCK [STR " + "; STR (string_of_big_int n)]) :: res, succ i, false)
	    else 
	      ((LBLOCK [STR " - "; STR (string_of_big_int (abs_big_int n))]) :: res, succ i, false)
	  else if first then 
	    ((LBLOCK [STR (string_of_big_int n); v#toPretty]) :: res, succ i, false)
	  else 
	    if gt_big_int n zero_big_int then 
	      ((LBLOCK [STR " + "; STR (string_of_big_int n); v#toPretty]) :: res, succ i, false)
	    else 
	      ((LBLOCK [STR " - ";
                        STR (string_of_big_int (abs_big_int n)); v#toPretty]) :: res, succ i, false) 
	end in
    let add_const res row = 
      let n = row.(pred ncols) in
      if eq_big_int n unit_big_int then STR " + 1" :: res
      else if eq_big_int n (minus_big_int unit_big_int) then STR " - 1" :: res
      else if gt_big_int n zero_big_int then (LBLOCK [STR " + "; STR (string_of_big_int n)]) :: res
      else (LBLOCK [STR " - "; STR (string_of_big_int (abs_big_int n))]) :: res in
    let output_row row = 
      let (res, _, _) = List.fold_left (output_list row) ([], 0, true) vars in
      let res = add_const res row in
      List.rev ((LBLOCK [STR (" " ^ rel ^ " 0"); NL]) :: res) in
    LBLOCK (List.flatten (List.map output_row (Array.to_list m)))


let has_row m a = 
  try
    for i = 0 to pred (Array.length m) do
      if equal_a m.(i) a then raise Exit
    done ;
    false
  with Exit -> true

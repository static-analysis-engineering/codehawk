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
open CHExternalValues
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHLogger
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm
open JCHJTDictionary

(* jchsys *)  
open JCHPrintUtils

(* jchcost *)
open JCHCostUtils
open JCHCostBound

let dbg = ref false

let instr_pc = ref (-1)
let set_instr_pc i = instr_pc := i
let get_instr_pc () = !instr_pc

let cmsix = ref (-1)
let set_cmsix i = cmsix := i

let st_lbs = ref (new CostBoundCollections.set_t)
let st_ubs =  ref (new CostBoundCollections.set_t)
let st_inf_lb = ref false
let st_inf_ub = ref false
let set_st_bounds lbs ubs inf_lb inf_ub =
  st_lbs := lbs;
  st_ubs := ubs ;
  st_inf_lb := inf_lb ;
  st_inf_ub := inf_ub
let get_st_bounds () = (!st_lbs, !st_ubs, !st_inf_lb, !st_inf_ub)

let cost_var_name = "$cost$"
    
let make_index_map boundss =
  let terms = new JTermTableCollections.set_t in 
  
  let get_terms (b: cost_bound_t) = terms#addList b#get_terms#listOfKeys in
  List.iter (fun bounds -> List.iter get_terms bounds) boundss; 

  let init_map =
    let t = new JTermCollections.table_t in
    t#set (JAuxiliaryVar cost_var_name) numerical_one ;
    [(0, t)] in

  let mk_index_map ts =
    let add_index_map (next, map) var = (succ next, (next, var) :: map) in
    snd (List.fold_left add_index_map (1, init_map) ts) in
  mk_index_map terms#toList

let get_linear_constraint_list
      index_map
      (lbs: cost_bound_t list)
      (ubs: cost_bound_t list) =
  List.rev_append
    (List.map (fun b -> b#to_linear_constraint index_map) lbs)
    (List.map (fun b -> b#to_linear_constraint index_map) ubs) 


let mk_poly_stage
      stage
      (lbs: cost_bound_t list)
      (ubs: cost_bound_t list)
      extra_constrs =
  (if !dbg then
     pr__debug [STR "mk_poly_stage "; INT stage; NL;
	        pp_list ubs; NL]);
  match stage with
  | 0 ->
     begin
       let index_map = make_index_map [lbs; ubs] in
       let constrs = get_linear_constraint_list index_map lbs ubs in
       try 
	 let poly = JCHPoly.mk_poly_from_constraints true (constrs@extra_constrs) in
	 (lbs, ubs, Some poly, index_map)
       with _ ->
	 chlog#add
           "too many rays"
	   (LBLOCK [STR "proc "; INT !cmsix; NL; STR "constrs: "; pp_list constrs; NL]) ;
	 (lbs, ubs, None, [])
     end
  | 1 ->
     begin
       let lbs = List.map (fun b -> b#make_small_div) lbs in
       let ubs = List.map (fun b -> b#make_small_div) ubs in
       let index_map = make_index_map [lbs; ubs] in
       let constrs = get_linear_constraint_list index_map lbs ubs in
       try 
	 let poly = JCHPoly.mk_poly_from_constraints true (constrs@extra_constrs) in
	 (lbs, ubs, Some poly, index_map)
       with _ -> (lbs, ubs, None, [])
     end
  | 2 ->
     begin
       let is_small b =
	 if b#is_small then
           true
	 else
	   begin
	     let pp =
               LBLOCK [STR "eliminated bound with large coefficients "; b#toPretty; NL] in
	     chlog#add "cost loss of precision" (LBLOCK [STR (pretty_to_string pp)]) ;
	     pr__debug [STR "cost loss of precision "; pp] ;
	     false
	   end in
       let lbs = List.filter is_small lbs in
       let ubs = List.filter is_small ubs in
       let index_map = make_index_map [lbs; ubs] in
       let constrs = get_linear_constraint_list index_map lbs ubs in
       try 
	 let poly = JCHPoly.mk_poly_from_constraints true (constrs@extra_constrs) in
	 (lbs, ubs, Some poly, index_map)
       with _ -> (lbs, ubs, None, [])
     end
  | 3 ->
     begin
       let has_few_terms b =
	 if b#number_terms < 100 then
           true
	 else
	   begin
	     let pp = LBLOCK [STR "eliminated bound with more than 100 terms "; NL] in
	     chlog#add "cost loss of precision" (LBLOCK [STR (pretty_to_string pp)]) ;
	     pr__debug [STR "cost loss of precision "; pp] ;
	     false
	   end in
       let lbs = List.filter has_few_terms lbs in
       let ubs = List.filter has_few_terms ubs in
       let index_map = make_index_map [lbs; ubs] in
       let constrs = get_linear_constraint_list index_map lbs ubs in
       try 
	 let poly =
           JCHPoly.mk_poly_from_constraints true (constrs@extra_constrs) in
	 (lbs, ubs, Some poly, index_map)
       with _ -> (lbs, ubs, None, [])
     end
  | _ ->
     ([], [], Some JCHPoly.top_poly, [])
    
let mk_poly
      stage (lbs: cost_bound_t list) (ubs: cost_bound_t list) extra_constrs =
  if !dbg then pr__debug [STR "mk_poly "; pp_list lbs; pp_list ubs; NL] ;
  let poly_opt = ref None in
  let lbs = ref lbs in
  let ubs = ref ubs in
  let index_map = ref [] in
  let stage = ref stage in
  
  while !poly_opt = None do 
    let (ls, us, p_opt, i_map) = mk_poly_stage !stage !lbs !ubs extra_constrs in
    check_cost_analysis_time (" while making poly in "^(string_of_int !cmsix)) ;
    poly_opt := p_opt ;
    lbs := ls;
    ubs := us ;
    index_map := i_map ;
    stage := !stage + 1
  done ;
  (Option.get !poly_opt, !index_map, !lbs, !ubs, !stage)

let eliminate_duplicates is_lb bounds =
  let (bounds_with_pos_terms, other_bounds) =
    List.partition (fun b -> b#has_pos_jterms) bounds in
  let new_bounds_with_pos_terms = ref [] in
  let add_bound bound =
    let is_better b =
      if b#equal bound then
        false
      else if is_lb then
        b#geq bound else
        b#leq bound in
    if List.exists is_better bounds_with_pos_terms then
      ()
    else
      new_bounds_with_pos_terms := bound :: !new_bounds_with_pos_terms in
  begin
    List.iter add_bound bounds_with_pos_terms ;
    !new_bounds_with_pos_terms @ other_bounds
  end

class cost_bounds_t
        ~(bottom: bool)
        ~(simplify: bool)
        ~(inflb: bool)
        ~(infub: bool)
        ~(lbounds: cost_bound_t list)
        ~(ubounds: cost_bound_t list) = 
object (self : 'a)
	  
  val bottom = ref bottom

  (* infinite cost. Example: the time cost of a method that is a 
   * server ; inf_lb -> inf_ub
   * An unknown cost is represented by top: not bottom or inf and 
   * no lbounds or ubounds *)
  val inf_lb = inflb 
  val inf_ub = infub

  val lbs = 
    if inflb then ref (new CostBoundCollections.set_t)
    else ref (CostBoundCollections.set_of_list lbounds)
    
  val ubs =
    if infub then ref (new CostBoundCollections.set_t)
    else ref (CostBoundCollections.set_of_list ubounds)

  initializer
    if simplify then
      try 
	let (lbs', ubs') = self#simplify lbounds ubounds in
	lbs := CostBoundCollections.set_of_list lbs';
	ubs := CostBoundCollections.set_of_list ubs'
      with _ ->
	(try
	  let (lbs', _) = self#simplify lbounds [] in
	  lbs := CostBoundCollections.set_of_list lbs'
	with _ -> lbs := new CostBoundCollections.set_t) ;
	(try
	  let (_, ubs') = self#simplify [] ubounds in
	  ubs := CostBoundCollections.set_of_list ubs'
	with _ -> ubs := new CostBoundCollections.set_t) 
	  
	  
  (* used to set lbs, ubs *)
  method kind =
    begin
      set_st_bounds !lbs !ubs inf_lb inf_ub ;
      "?"
    end
    
  method isBottom = !bottom
      
  method isTop =
    (not !bottom && not inf_lb && not inf_ub && !lbs#isEmpty && !ubs#isEmpty)

  method toPretty =
    if !bottom then
      STR "_|_"
    else if self#isTop then
      STR "T"
    else
      LBLOCK [STR "       lower bounds: ";
              if inf_lb then STR "oo" else !lbs#toPretty; NL;
	      STR "       upper bounds: ";
              if inf_ub then STR "oo" else !ubs#toPretty; NL]

  method private mkBottom =
    {< bottom = ref true ;
       inf_lb = false;
       inf_ub = false;
       lbs = ref (new CostBoundCollections.set_t);
       ubs = ref (new CostBoundCollections.set_t) >}
    
  method private mkTop =
    {< bottom = ref false;
       inf_lb = false; 
       inf_ub = false; 
       lbs = ref (new CostBoundCollections.set_t);
       ubs = ref (new CostBoundCollections.set_t) >}

  method private mk_inf_lb =
    {< bottom = ref false;
       inf_lb = true; 
       inf_ub = true; 
       lbs = ref (new CostBoundCollections.set_t);
       ubs = ref (new CostBoundCollections.set_t) >}
    
  method private find_index
      (index_map: (int * numerical_t JTermCollections.table_t) list)
      (term: numerical_t JTermCollections.table_t) = 
    try
      let comp = compare_tables jterm_compare compare_num in
      fst (List.find (fun (_, t) -> comp term t = 0) index_map)
    with
    | Not_found ->
       raise (JCH_failure
		(LBLOCK [ term#toPretty;
                          STR " not found in JCHCostBounds.find_index" ]))
      
  method private simplify
                   (lbs': cost_bound_t list) (ubs': cost_bound_t list) =
    
    (if !dbg then
       pr__debug [STR "simplify "; pp_list lbs'; pp_list ubs'; NL]) ;
    
    let (lbs', ubs') =
      (eliminate_duplicates true lbs', eliminate_duplicates false ubs') in
    let (poly, index_map, _, _, _) = mk_poly 0 lbs' ubs' [] in

    if poly#is_bottom then
      begin
	bottom := true;
	([], [])
      end
    else if List.length lbs' <= 1 && List.length ubs' <= 1 then
      (lbs', ubs')
    else
      begin
	(if !dbg then
           pr_debug [STR "simplify poly = "; NL; poly#toPretty; NL]) ;
        
	let constrs = poly#get_constraints in
        
	(if !dbg then
           pr_debug [STR "constrs = "; pp_list constrs; NL]) ;
        
	let bounds =
          List.concat
            (List.map (bounds_from_linear_constraint index_map) constrs) in
	let (lbs_list, ubs_list) = List.partition (fun b -> b#is_lb) bounds in
	let (lbs_const, lbs_not_const) =
          List.partition (fun b -> b#is_const) lbs_list in
	let lbs_list =
	  if List.length lbs_const <= 1 then lbs_list
	  else
	    begin
	      (if !dbg then
                 pr_debug [STR "lbs_const = ";  pp_list lbs_const; NL]);
              
	      let sorted_consts = List.sort compare lbs_const in
	      let pp = LBLOCK [STR "eliminated const bounds ";
                               pp_list (List.tl sorted_consts); NL] in
	      chlog#add
                "cost loss of precision"
                (LBLOCK [STR (pretty_to_string pp)]) ;
              
	      pr__debug [STR "cost loss of precision "; pp] ;
              
	      (List.hd sorted_consts) :: lbs_not_const
	    end in
	(if !dbg then
           pr_debug [STR "lbs_list = "; pp_list lbs_list; NL]) ;
        
	let (ubs_const, ubs_not_const) =
          List.partition (fun b -> b#is_const) ubs_list in
	let ubs_list =
	  if List.length ubs_const <= 1 then ubs_list
	  else
	    begin
	      let sorted_consts = List.rev (List.sort compare ubs_const) in
	      let pp = LBLOCK [STR "eliminated const bounds ";
                               pp_list (List.tl sorted_consts); NL] in
	      chlog#add
                "cost loss of precision"
                (LBLOCK [STR (pretty_to_string pp)]) ;
              
	      pr__debug [STR "cost loss of precision "; pp] ;
              
	      (if !dbg then
                 pr_debug [STR "ubs_const = ";  pp_list ubs_const; NL]);
              
	      (List.hd sorted_consts) :: ubs_not_const
	    end in
	(if !dbg then
           pr_debug [STR "ubs_list = "; pp_list ubs_list; NL]) ;
        
	(lbs_list, ubs_list)
      end
      
  method private check_is_bottom
                   (bs1: cost_bound_t list) (bs2: cost_bound_t list) =
    (if !dbg then
       pr__debug [STR "check_is_bottom"; NL]) ;
    
    let (poly, _, _, _, _) = mk_poly 0 bs1 bs2 [] in
    poly#is_bottom 

  method private check_bounds_inclusion
                   ~(upper_bounds:bool)
                   ~(bs1: cost_bound_t list)
                   ~(bs2: cost_bound_t list)
                   ~(inf1: bool)
                   ~(inf2: bool) =
    match (inf1, inf2) with
    | (true, true) -> true
    | (true, false) -> not upper_bounds
    | (false, true) -> upper_bounds
    | (false, false) ->
	let check_one (b2: cost_bound_t) =
	  if upper_bounds then
            self#check_is_bottom [b2#make_opposite] bs1
	  else
            self#check_is_bottom bs1 [b2#make_opposite] in
	List.for_all check_one bs2 

  method private get_bounds a =
    let _ = a#kind in
    get_st_bounds ()

  method private get_jterms (a: 'a) =
    let (albs, aubs, _, _) = self#get_bounds a in
    let set = new JTermCollections.set_t in
    let add_vars c = set#addSet c#get_jterms in
    albs#iter add_vars ;
    aubs#iter add_vars ;
    set
      
  method equal (a: 'a) =
    let (albs, aubs, ainf_lb, ainf_ub) = self#get_bounds a in
    match (!bottom, a#isBottom) with
    | (true, true) 
    | (false, false) ->
	(inf_lb == ainf_lb) && (inf_ub == ainf_ub) && self#leq a && a#leq self
    | _ -> false
	  
  method leq (a: 'a) =
    let (albs, aubs, ainf_lb, ainf_ub) = self#get_bounds a in
    match (!bottom, a#isBottom) with 
      | (true, _) -> true
      | (_, true) -> false
      | (false, false) ->
	 (self#check_bounds_inclusion
            ~upper_bounds:false
            ~bs1:!lbs#toList
            ~bs2:albs#toList
            ~inf1:inf_lb
            ~inf2:ainf_lb)
         && (self#check_bounds_inclusion
               ~upper_bounds:true
               ~bs1:!ubs#toList
               ~bs2:aubs#toList
               ~inf1:inf_ub
               ~inf2:ainf_ub)

  method meet (a: 'a) =
    
    (if !dbg then
      pr__debug [STR "meet "; NL; STR "   "; self#toPretty; NL;
                 STR "   "; a#toPretty; NL]) ;
    
    let (albs, aubs, ainf_lb, ainf_ub) = self#get_bounds a in
    match (!bottom, a#isBottom, inf_lb, ainf_lb) with
      | (true, _, _, _) -> self#mkBottom
      | (_, true, _, _) -> self#mkBottom
      | (false, false, true, _) -> a
      | (false, false, _, true) ->
	  let new_lbs = !lbs#union albs in
	  let (poly, index_map, _, _, _) = mk_poly 0 new_lbs#toList [] [] in
	  self#mk_from_poly index_map poly true
      | (false, false, false, false) ->
	  let new_lbs = !lbs#union albs in
	  let new_ubs = !ubs#union aubs in
	  let (poly, index_map, _, _, _) =
            mk_poly 0 new_lbs#toList new_ubs#toList [] in
	  self#mk_from_poly index_map poly false

  (* adds only one constant bound *)	        
  method private mk_bound_set_from_list lb list =
    let set = new CostBoundCollections.set_t in
    let const_bound = ref None in
    
    let is_smaller (c, d) (c1, d1) = (c#mult d1)#leq (c1#mult d) in
	
    let add_element b =
      if b#is_const then
	match !const_bound with
	| Some (b1, c1, d1) ->
	    let (c, d) = (b#get_const, b#get_div) in
	    if lb then
	      if is_smaller (c, d) (c1, d1) then ()
	      else 
		begin
		  const_bound := Some (b, c, d) ;
		  set#remove b1;
		  set#add b
		end
	    else
	      if is_smaller (c, d) (c1, d1) then
		begin
		  const_bound := Some (b, c, d) ;
		  set#remove b1;
		  set#add b
		end
	      else
                ()
	| _ ->
           begin
	     const_bound := Some (b, b#get_const, b#get_div);
	     set#add b
           end
      else
        set#add b in

    begin
      List.iter add_element list ;
      set
    end
	
  method private mk_from_poly index_map poly inf_ub =
    
    (if !dbg then
       pr__debug [STR "mk_from_poly "; NL]) ;
    
    if poly#is_bottom then
      self#mkBottom
    else
      begin
	let constrs = poly#get_constraints in
	let poly_index_map = poly#get_index_map in
        
	(if !dbg then
           pr__debug [STR "poly_index_map = ";
                      pp_assoc_list_ints poly_index_map; NL]) ;
        
	(if !dbg then
           pr__debug [STR "index_map = ";
                      pp_list_int (List.map fst index_map);
                      STR " "; pp_list (List.map snd index_map); NL]) ;
        
	let eq_constrs = List.filter (fun c -> c#is_const_equality) constrs in
	let eq_inds = ref [] in
	let new_index_map = ref index_map in
	let add_eq (constr: JCHLinearConstraint.linear_constraint_t) =
	  if !dbg then pr__debug [STR "add_eq "; constr#toPretty; NL] ;
	  let (pairs, _) = constr#get_pairs_const in
	  let (ind, _) = List.hd pairs in
	  if ind != 0 then
	    begin
              
	      (if !dbg then
                 pr__debug [STR "ind = "; INT ind; NL]) ;
              
	      eq_inds := ind :: !eq_inds ;
	      new_index_map :=
                List.filter (fun (i, _) -> i != ind) !new_index_map
	    end in
	List.iter add_eq eq_constrs ;
	let res_poly = poly#project_out !eq_inds in
	let constrs = res_poly#get_constraints in
	let bounds =
          List.concat
            (List.map (bounds_from_linear_constraint !new_index_map) constrs) in
	let (lbs, ubs) = List.partition (fun b -> b#is_lb) bounds in
	if inf_ub then
	  {< bottom = ref false;
	    inf_lb = false;
	    inf_ub = true;
	    lbs = ref (self#mk_bound_set_from_list true lbs);
	    ubs = ref (new CostBoundCollections.set_t) >}
	else 
	  {< bottom = ref false;
	    inf_lb = false;
	    inf_ub = false;
	    lbs = ref (self#mk_bound_set_from_list true lbs);
	    ubs = ref (self#mk_bound_set_from_list false ubs) >}
      end

(* assume that the cost bounds have only one lower and upper bound each
 * and that these upper and lower bounds have positive coefficients and 
 * positive terms *)
  method join (a: 'a) =
    
    (if !dbg then
       pr__debug [STR "join "; NL; STR "   "; self#toPretty; NL;
		  STR "   "; a#toPretty; NL]) ;
    
    let (albs, aubs, ainf_lb, ainf_ub) = self#get_bounds a in
    match (!bottom, a#isBottom, self#isTop, a#isTop, inf_lb, ainf_lb) with
      | (true, _, _, _, _, _) -> a
      | (_, true, _, _, _, _) -> {< >}
      | (false, false, true, _, _, _)
      | (false, false, _, true, _, _) ->  self#mkTop
      | (false, false, false, false, true, _)
      | (false, false, false, false, _, true) -> self#mk_inf_lb
      | (false, false, false, false, false, false) ->
	  let new_inf_ub = inf_ub || ainf_ub in
	    
	  let (lbs, ubs, albs, aubs) =
	    if new_inf_ub then
              (!lbs#toList, [], albs#toList, [])
            else
              (!lbs#toList, !ubs#toList, albs#toList, aubs#toList) in

	  if (List.length albs) > 1 then
	    begin
	      let pp = LBLOCK [STR "ignored bound in join ";
                               pp_list (List.tl albs); NL] in
	      chlog#add
                "cost loss of precision"
                (LBLOCK [STR (pretty_to_string pp)]) ;
              
	      pr__debug [STR "cost loss of precision "; pp] ;
	    end ;
	  if (List.length aubs) > 1 then
	    begin
	      let pp = LBLOCK [STR "ignored bound in join ";
                               pp_list (List.tl aubs); NL] in
	      chlog#add
                "cost loss of precision"
                (LBLOCK [STR (pretty_to_string pp)]) ;
              
	      pr__debug [STR "cost loss of precision "; pp] ;
	    end ;
	  let rlb = (List.hd lbs)#simple_join (List.hd albs) in
	  let rub = (List.hd ubs)#simple_join (List.hd aubs) in
	  {< bottom = ref false;
	    inf_lb = false;
	    inf_ub = false;
	    lbs = ref (CostBoundCollections.set_of_list [rlb]);
	    ubs = ref (CostBoundCollections.set_of_list [rub]) >} 
	    
  method widening (a: 'a) =
    
    (if !dbg then
      pr__debug [STR "widening "; NL; STR "   "; self#toPretty; NL;
                 STR "   "; a#toPretty; NL]) ;
    
    let (albs, aubs, ainf_lb, ainf_ub) = self#get_bounds a in
    match (!bottom, a#isBottom, self#isTop, a#isTop, inf_lb, ainf_lb) with
      | (true, _, _, _, _, _) -> a
      | (_, true, _, _, _, _) -> {< >}
      | (false, false, true, _, _, _)
      | (false, false, _, true, _, _) ->  self#mkTop
      | (false, false, false, false, true, _)
      | (false, false, false, false, _, true) -> self#mk_inf_lb
      | (false, false, false, false, false, false) ->
	  let new_inf_ub = inf_ub || ainf_ub in
	  let (lbs, ubs, albs, aubs) =
	    if new_inf_ub then (!lbs#toList, [], albs#toList, [])
	    else (!lbs#toList, !ubs#toList, albs#toList, aubs#toList) in
	  let bs = lbs @ ubs in
	  let abs = albs @ aubs in
	  let lbs_i =
            List.filter (fun b ->
                self#check_bounds_inclusion
                  ~upper_bounds:false
                  ~bs1:[b]
                  ~bs2:abs
                  ~inf1:false
                  ~inf2:false) lbs in
	  let ubs_i =
            List.filter (fun b ->
                self#check_bounds_inclusion
                  ~upper_bounds:false
                  ~bs1:[b]
                  ~bs2:abs
                  ~inf1:false
                  ~inf2:false) ubs in
	  let albs_i =
            List.filter (fun b ->
                self#check_bounds_inclusion
                  ~upper_bounds:true
                  ~bs1:[b]
                  ~bs2:bs
                  ~inf1:false
                  ~inf2:false) albs in
	  let aubs_i =
            List.filter (fun b ->
                self#check_bounds_inclusion
                  ~upper_bounds:true
                  ~bs1:[b]
                  ~bs2:bs
                  ~inf1:false
                  ~inf2:false) aubs in
	  {< bottom = ref false ;
	    inf_lb = false;
	    inf_ub = false;
	    lbs = ref (CostBoundCollections.set_of_list (lbs_i @ albs_i)) ;
	    ubs = ref (CostBoundCollections.set_of_list (ubs_i @ aubs_i)) >}
	    
  method narrowing (a: 'a) =
    self#meet a

  method marshal =
    match (!bottom, inf_lb) with
    | (true, _) -> EVX_STRING "_|_"
    | (_, true) -> EVX_STRING "oo"
    | _ -> 
	EVX_LIST
	  [ EVX_LIST (List.map (fun b -> b#to_evx) !lbs#toList);
	    EVX_LIST (List.map (fun b -> b#to_evx) !ubs#toList)]


end

let bottom_cost_bounds =
  new cost_bounds_t
      ~bottom:true
      ~simplify:false
      ~inflb:false
      ~infub:false
      ~lbounds:[]
      ~ubounds:[]
    
let top_cost_bounds =
  new cost_bounds_t
      ~bottom:false
      ~simplify:false
      ~inflb:false
      ~infub:false
      ~lbounds:[]
      ~ubounds:[]
    
let cost_bounds_from_num n =
  new cost_bounds_t
      ~bottom:false
      ~simplify:false
      ~inflb:false
      ~infub:false
      ~lbounds:[cost_bound_from_num true n]
      ~ubounds:[cost_bound_from_num false n]

let inf_lb_cost_bounds =
  new cost_bounds_t
      ~bottom:false
      ~simplify:false
      ~inflb:true
      ~infub:true
      ~lbounds:[]
      ~ubounds:[]

let cost_var =
  let name = new symbol_t ~atts:["num"] "$cost$" in
  new variable_t name NUM_VAR_TYPE

let cost_jterm = JAuxiliaryVar "$cost$"

let cost_bounds_from_jterm_range (r: jterm_range_int) =
  
  (if !dbg then
     pr__debug [STR "cost_bounds_from_jterm_range "; NL; r#toPretty; NL]);
  
  let lbounds = r#get_lowerbounds in
  let ubounds = r#get_upperbounds in
  let lower_cost_bounds = List.map (bound_from_jterm true) lbounds in
  let upper_cost_bounds = List.map (bound_from_jterm false) ubounds in
  new cost_bounds_t
      ~bottom:false
      ~simplify:true
      ~inflb:false
      ~infub:false
      ~lbounds:lower_cost_bounds
      ~ubounds:upper_cost_bounds
      
let get_bounds bounds =
  begin
    bounds#kind;
    get_st_bounds ()
  end

let add_cost_bounds (s: cost_bounds_t) (a: cost_bounds_t) =
  
  (if !dbg then
    pr__debug [STR "add_cost_bounds "; NL;
               STR "     "; s#toPretty; STR " "; a#toPretty; NL]);
  
  let (slbs, subs, sinf_lb, sinf_ub) = get_bounds s in
  let (albs, aubs, ainf_lb, ainf_ub) = get_bounds a in
  match (s#isBottom, a#isBottom, sinf_lb, ainf_lb) with
  | (true, _, _, _) -> bottom_cost_bounds
  | (_, true, _, _) -> bottom_cost_bounds
  | (false, false, true, _) 
  | (false, false, _, true) -> inf_lb_cost_bounds
  | (false, false, false, false) ->
      let new_inf_ub = sinf_ub || ainf_ub in
      let (slbs, subs, albs, aubs) =
        (slbs#toList, subs#toList, albs#toList, aubs#toList) in
      let new_lbs = ref [] in
      let new_ubs = ref [] in
      let add_bound lower_bounds b1 b2 =
	if lower_bounds then
          new_lbs := (b1#add b2) :: !new_lbs
	else
          new_ubs := (b1#add b2) :: !new_ubs in
      let add_bounds lower_bounds bs1 bs2 =
	List.iter
          (fun b1 -> (List.iter (fun b2 -> add_bound lower_bounds b1 b2) bs2))
          bs1 in
      begin
        add_bounds true slbs albs;
        if not new_inf_ub then
          add_bounds false subs aubs;
        
        (if !dbg then
           pr__debug [STR "new_lbs = "; pp_list !new_lbs; NL]) ;
        
        (if !dbg then
           pr__debug [STR "new_ubs = "; pp_list !new_ubs; NL]) ;
        
        new cost_bounds_t false false false new_inf_ub !new_lbs !new_ubs
      end

let neg_cost_bounds (s: cost_bounds_t) =
  if s#isBottom then bottom_cost_bounds
  else
    let (slbs, subs, inf_lb, inf_ub) = get_bounds s in
    let new_lbs = List.map (fun ub -> ub#neg) subs#toList in
    let new_ubs = List.map (fun lb -> lb#neg) slbs#toList in
    new cost_bounds_t
        ~bottom:false
        ~simplify:false
        ~inflb:false
        ~infub:false
        ~lbounds:new_lbs
        ~ubounds:new_ubs
    
let sub_cost_bounds (s: cost_bounds_t) (a: cost_bounds_t) =
  add_cost_bounds s (neg_cost_bounds a)

let mult_cost_bounds (s: cost_bounds_t) (a: cost_bounds_t) =
  
  (if !dbg then
     pr__debug [STR "mult_cost_bouds "; NL; STR "     "; s#toPretty; NL;
	        STR "      "; a#toPretty; NL]) ;
  
  let (slbs, subs, sinf_lb, sinf_ub) = get_bounds s in
  let (albs, aubs, ainf_lb, ainf_ub) = get_bounds a in
  match (s#isBottom, a#isBottom, sinf_lb, ainf_lb) with
    | (true, _, _, _) -> bottom_cost_bounds
    | (_, true, _, _) -> bottom_cost_bounds
    | (false, false, true, _) 
    | (false, false, _, true) -> inf_lb_cost_bounds
    | (false, false, _, _) ->
	let new_inf_ub = sinf_ub || ainf_ub in
	let (slbs, subs, albs, aubs) =
          (slbs#toList, subs#toList, albs#toList, aubs#toList) in
	let new_lbs = ref [] in
	let new_ubs = ref [] in
	let mult_bound lower_bounds b1 b2 =
	  if lower_bounds then new_lbs := (b1#mult b2) :: !new_lbs
	  else new_ubs := (b1#mult b2) :: !new_ubs in
	let mult_bounds lower_bounds bs1 bs2 =
	  List.iter (fun b1 ->
              (List.iter (fun b2 -> mult_bound lower_bounds b1 b2) bs2)) bs1 in
        begin
	  mult_bounds true slbs albs;
	  mult_bounds true albs slbs;
	  (if not new_inf_ub then
	    begin
	      mult_bounds false subs aubs;
	      mult_bounds false aubs subs
	    end) ;
	  new cost_bounds_t
              ~bottom:false
              ~simplify:false
              ~inflb:false
              ~infub:new_inf_ub
              ~lbounds:!new_lbs
              ~ubounds:!new_ubs
        end

let div_cost_bounds (s: cost_bounds_t) (a: cost_bounds_t) =
  let (slbs, subs, sinf_lb, sinf_ub) = get_bounds s in
  let (albs, aubs, ainf_lb, ainf_ub) = get_bounds a in
  match (s#isBottom, a#isBottom, sinf_lb) with
    | (true, _, _) -> bottom_cost_bounds
    | (_, true, _) -> bottom_cost_bounds
    | (false, false, true) -> s
    | (false, false, false) ->
       let (slbs, subs, albs, aubs) =
         (slbs#toList, subs#toList, albs#toList, aubs#toList) in
	let is_non0_const b = b#is_non_0_const in
	let albs_const = List.filter is_non0_const albs in
	let aubs_const = List.filter is_non0_const aubs in
	let new_lbs = ref [] in
	let new_ubs = ref [] in
	let div_bound lower_bounds b1 b2 =
	  if lower_bounds then
            new_lbs := (b1#div b2) :: !new_lbs
	  else
            new_ubs := (b1#div b2) :: !new_ubs in
	let div_bounds lower_bounds bs1 bs2 =
	  List.iter
            (fun b1 -> (List.iter (fun b2 -> div_bound lower_bounds b1 b2) bs2))
            bs1 in
        begin
	  div_bounds true slbs albs_const;
	  (if not sinf_ub then
             div_bounds false subs aubs_const);
	  new cost_bounds_t
              ~bottom:false
              ~simplify:false
              ~inflb:false
              ~infub:sinf_ub
              ~lbounds:!new_lbs
              ~ubounds:!new_ubs
        end

let write_xml_bounds
      ?(tag="ijtr") (s:cost_bounds_t) (node:xml_element_int) =
  let (lbs,ubs, inf_lb, inf_ub) = get_bounds s in
  let bool_to_str b = if b then "true" else "false" in
  node#setAttribute "bottom" (bool_to_str s#isBottom) ;
  node#setAttribute "inf_lb" (bool_to_str inf_lb) ;
  node#setAttribute "inf_ub" (bool_to_str inf_ub) ;
  let lbs = List.map (fun b -> b#to_jterm) lbs#toList in
  let ubs = List.map (fun b -> b#to_jterm) ubs#toList in
  jtdictionary#write_xml_jterm_range ~tag node lbs ubs

let write_xml_atlas_bounds
      (node:xml_element_int) (ms:method_signature_int) (b:cost_bounds_t) =
  let (lbs,ubs,inf_lb,inf_ub) = get_bounds b in
  let lbs = List.map (fun b -> b#to_jterm) lbs#toList in
  let ubs = List.map (fun b -> b#to_jterm) ubs#toList in
  let jtrange = mk_jterm_range lbs ubs in  
  let set = node#setAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let _ = sety "bottom" b#isBottom in
  match jtrange#to_constant with
  | Some n -> set "value" n#toString
  | _ ->
     begin
       (match jtrange#get_lowerbounds with
        | [ JConstant n ] -> set "lb" n#toString
        | _ -> ()) ;
       (match jtrange#get_upperbounds with
        | [ JConstant n ] -> set "ub" n#toString
        | _ -> ()) ;
       (match jtrange#to_jterm with
        | Some t when (depth_of_jterm t) < 6 ->
           node#appendChildren [ jterm_to_xmlx t ms ]
        | _ -> ())
     end
  
  
let bounds_from_jterms simplify lb_jterms ub_jterms =
  
  (if !dbg then
     pr__debug [ STR "bounds_from_jterms "; pp_bool simplify; 
	         pp_list_jterm lb_jterms; STR " ";
                 pp_list_jterm ub_jterms; NL]) ;
  
  let lbs = List.map (fun j -> bound_from_jterm true j) lb_jterms in
  let ubs = List.map (fun j -> bound_from_jterm false j) ub_jterms in
  new cost_bounds_t
      ~bottom:false
      ~simplify
      ~inflb:false
      ~infub:false
      ~lbounds:lbs
      ~ubounds:ubs

let read_xml_bounds ?(tag="ibcost") (node:xml_element_int):(cost_bounds_t) =
  let (lbs, ubs) = jtdictionary#read_xml_jterm_range ~tag node in
  let block_cost = bounds_from_jterms true lbs ubs in
  block_cost

let bounds_from_jterm_range simplify (jterm_range:jterm_range_int) =
  bounds_from_jterms
    simplify jterm_range#get_upperbounds jterm_range#get_lowerbounds

(* assume that all bounds in lmap, umap represent positive quantities or
 * that cost_bounds is linear *)
let subst_in_cost_bounds
      ~(pc:int)
      ~(cost_bounds: cost_bounds_t)
      ~(use_one_bound: bool)
      ~(lmap: (jterm_t * cost_bound_t list) list)
      ~(umap: (jterm_t * cost_bound_t list) list)
      ~(inf_lbs : jterm_t list) 
      ~(inf_ubs : jterm_t list)
      ~(subst_only_local_vars: bool)
      ~(subst_only_lps: bool)
      ~(subst_all: bool): cost_bounds_t =

  let get_best_bounds
        lower_bounds (bs:cost_bound_t list):cost_bound_t list =
    
    (if !dbg then
      pr__debug [STR "get_best_bounds ";
                 pretty_print_list
                   bs (fun b -> STR b#to_string) "{" "; " "}"; NL]) ;
    
    let bounds = eliminate_duplicates lower_bounds bs in
    
    (if !dbg then
       pr__debug [ STR "bounds = ";
                   pretty_print_list
                     bounds (fun b -> STR b#to_string) "{" "; " "}"; NL]) ;
    
    if List.length bounds < 2 then
      bounds
    else
      let res_bounds = 
	let (bs, ignored_bs) =
	  let (neg_bs, pos_bs) =
            List.partition (fun b -> b#has_negative_coefficient) bounds in
	  if pos_bs <> [] then
            (pos_bs, neg_bs)
	  else
            (neg_bs, []) in
	if List.length bs < 2 then
          bs
	else
	  begin
	    let bs =
	      let has_max (b: JCHCostBound.cost_bound_t) =
		List.exists (fun j ->
                    jterm_compare j sym_max_int = 0
                    || jterm_compare j sym_max_long = 0) b#get_jterms#toList in
	      let (bs_with_max, bs_wo_max) = List.partition has_max bs in
	      if bs_wo_max <> [] then bs_wo_max else bs_with_max in
	    let (kept_bs, ignored_bs) = 
	      if List.length bs < 2 then
                (bs, ignored_bs)
	      else
		begin
		  let bs =
                    List.sort (fun b1 b2 ->
                        compare b1#get_terms#size b2#get_terms#size) bounds in
		  ([List.hd bs], (List.tl bs) @ ignored_bs)
		end in
	    if ignored_bs != [] then
	      begin
		let method_name =
                  (retrieve_cms !cmsix)#class_method_signature_string in
		let pp =
                  LBLOCK [ STR method_name; STR " @ "; INT pc; NL;
			   STR "         used bound "; STR (List.hd bs)#to_string; NL;
			   STR "         ignored ";
                           pretty_print_list
                             ignored_bs (fun b -> STR b#to_string) "{" "; " "}"; NL] in
		chlog#add
                  "cost loss of precision"
                  (LBLOCK [STR (pretty_to_string pp)]) ;
                
		pr__debug [STR "cost loss of precision "; pp]
                
	      end ;
	    kept_bs 
	  end in
      res_bounds in

  let (lbs, ubs, inf_lb, inf_ub) = get_bounds cost_bounds in
  
  (if !dbg then
     begin
       pr__debug [STR "after add_consts, subst_in_cost_bounds ";
                  pp_bool subst_only_local_vars; STR " ";
                  pp_bool subst_only_lps;  NL;
		  cost_bounds#toPretty; NL] ;
       pr__debug [STR "lmap: "; NL];
      List.iter
        (fun (jt, ls) ->
          pr__debug [jterm_to_pretty jt; STR ": "; pp_list ls; NL]) lmap;
      pr__debug [STR "umap: "; NL];
      List.iter
        (fun (jt, ls) ->
          pr__debug [jterm_to_pretty jt; STR ": "; pp_list ls; NL]) umap
     end) ;
  
  if cost_bounds#isBottom || inf_lb then
    cost_bounds
  else
    begin
      
      (if !dbg then
	 begin
	   let pr_list is_lb (jterm, cbs) =
	     pr__debug [jterm_to_pretty jterm;
                        STR (if is_lb then " >= " else "<=");
                        pp_list cbs; NL] in
	   List.iter (pr_list true) lmap;
	   List.iter (pr_list false) umap
	 end) ;
      
      let has_inf_jterm is_lb (bound: cost_bound_t) =
	let jts = bound#get_jterms in
	let infs = if is_lb then inf_lbs else inf_ubs in
	List.exists (fun inf ->jts#has inf) infs in

      let inf_lb = inf_lb || (List.exists (has_inf_jterm true) lbs#toList) in
      let inf_ub = inf_ub || (List.exists (has_inf_jterm false) ubs#toList) in

      let is_jterm_to_keep =
	if subst_only_local_vars then
          JCHCostUtils.no_local_vars
	else if subst_only_lps then
          JCHCostUtils.no_loop_costs
	else 
	  let lcs_with_ubounds =
	    JTermCollections.set_of_list
              (List.map
                 fst
                 (List.filter
                    (fun (jt, bs) -> (is_sym_lc jt && bs != [])) umap)) in
	  if subst_all then
            JCHCostUtils.no_cost_calls_or_lcs lcs_with_ubounds 
	  else
            JCHCostUtils.no_calls_or_lcs lcs_with_ubounds in

      (if !dbg then pr__debug [STR "lbs = "; lbs#toPretty; NL]);
      
      (if !dbg then pr__debug [STR "ubs = "; ubs#toPretty; NL]);
      
      let (lbs_t, lbs_f) =
        List.partition
          (fun b -> b#has_only_jterms_to_keep is_jterm_to_keep) lbs#toList in 
      let (ubs_t, ubs_f) =
        List.partition
          (fun b -> b#has_only_jterms_to_keep is_jterm_to_keep) ubs#toList in
      
      (if !dbg then
         pr__debug [STR "lbs_with_jterms_to_remove = "; pp_list lbs_f; NL]) ;
      
      (if !dbg then
         pr__debug [STR "ubs_with_jterms_to_remove = "; pp_list ubs_f; NL]) ;

      let mk_list mp =
	let choices : ((jterm_t * 'a) list list) ref = ref [] in
	let add_choice (j, bs) =
          
	  (if !dbg && (List.length bs > 1) then
	     pr__debug [STR "mk_list "; jterm_to_pretty j;
                        STR " "; pp_list bs; NL]) ;
          
	  let add_to_choice choice : ((jterm_t * 'a) list list) = 
	    List.map (fun b -> (j,b) :: choice) bs in
	  choices :=
	    if !choices = [] then
              (List.map (fun b -> [(j,b)]) bs) 
	    else
              List.concat
		(List.map add_to_choice !choices) in
	List.iter add_choice (List.filter (fun (_, ls) -> ls != []) mp) ;
	!choices in
      let lchoices =
	let lmap =
	  if use_one_bound then
	    List.map (fun (j, bs) -> (j, get_best_bounds true bs)) lmap
          else
            lmap in
	mk_list lmap in
      let uchoices =
	let umap =
	  if use_one_bound then
	    List.map (fun (j, bs) -> (j, get_best_bounds false bs)) umap
          else
            umap in
	mk_list umap in

      (if !dbg then
         pr__debug [STR "lchoices size = "; INT (List.length lchoices); NL]);
      
      (if !dbg then
         pr__debug [STR "uchoices size = "; INT (List.length uchoices); NL]);

      let subst_in_bound
            (choices: ((jterm_t * 'a) list list))
            (other_choices: ((jterm_t * 'a) list list))
            (b: cost_bound_t) =
	if b#has_pos_coeffs then
          b#subst choices is_jterm_to_keep
	else
	  let (b_pos, b_neg) = b#split_pos_neg in
	  let new_bs_pos = b_pos#subst choices is_jterm_to_keep in
	  let new_bs_neg = b_neg#subst other_choices is_jterm_to_keep in
	  List.flatten
            (List.map (fun pos_b ->
                 List.map (fun neg_b -> pos_b#sub neg_b) new_bs_neg) new_bs_pos) in
	
      let new_lbs = List.map (subst_in_bound lchoices uchoices) lbs_f in
      let new_lbs = List.concat (lbs_t :: new_lbs) in
      let new_ubs = List.map (subst_in_bound uchoices lchoices) ubs_f in
      let new_ubs = List.concat (ubs_t :: new_ubs) in
      new cost_bounds_t false true inf_lb inf_ub new_lbs new_ubs
    end


let pos_jterm_table = new JTermCollections.table_t
(* jterm -> cost bounds for jterm dependent on 
 * sym_cost's, sym_call's, sym_lp's and sym_lc's *)
                    
let pos_jterm_table_final = new JTermCollections.table_t
(* jterm -> cost bounds for jterm dependent only on sym_lc's *)

let is_const_range cost_bounds =
  
  (if !dbg then
     pr__debug [STR "is_const_range "; cost_bounds#toPretty; NL]);
  
  let res = 
    let (lbs, ubs, inf_lb, inf_ub) = get_bounds cost_bounds in
    match (lbs#toList, ubs#toList) with
    | ([lb], [ub]) -> lb#is_const && ub#is_const
    | _ -> false in
  
  (if !dbg then
     pr__debug [STR "is_const_range res = "; pp_bool res; NL]) ;
  res
      
	
let get_jterms cost_bounds =
  let (lbs, ubs, _, _) = get_bounds cost_bounds in
  let set = new JTermCollections.set_t in
  let add_bound b = set#addSet b#get_jterms in
  begin
    lbs#iter add_bound;
    ubs#iter add_bound;
    set#toList 
  end

let subst_pos_bounds_ pc cost_bounds only_lps use_pos_jterm_final =
  
  (if !dbg then
     pr_debug [STR "subst_pos_bounds_ "; pp_bool only_lps; STR " ";
               pp_bool use_pos_jterm_final; NL;
               cost_bounds#toPretty; NL]) ;
  
  if is_const_range cost_bounds then
    cost_bounds
  else
    begin
      let lbounds = ref [] in
      let ubounds = ref [] in
      let inf_lbs = ref [] in
      let inf_ubs = ref [] in
      let jterm_table =
        if use_pos_jterm_final then
          pos_jterm_table_final else pos_jterm_table in
      
      (if !dbg then
         pr__debug [STR "jterm_table = "; NL; jterm_table#toPretty; NL]) ;
      
      let add_jt jterm =
	if only_lps && not (is_sym_lp jterm) then
          ()
	else
	  begin
	    match jterm_table#get jterm with
	    | Some cbounds ->
	       let (lbs, ubs, inf_lb, inf_ub) = get_bounds cbounds in
               begin
		 lbounds := (jterm, lbs#toList) :: !lbounds;
		 ubounds := (jterm, ubs#toList) :: !ubounds;
		 (if inf_lb then inf_lbs := jterm :: !inf_lbs) ;
		 (if inf_ub then inf_ubs := jterm :: !inf_ubs)
               end
	    | _ -> ()
	  end in
      List.iter add_jt (get_jterms cost_bounds) ;
      subst_in_cost_bounds
        ~pc
        ~cost_bounds
        ~use_one_bound:true
        ~lmap:!lbounds
        ~umap:!ubounds
        ~inf_lbs:!inf_lbs
        ~inf_ubs:!inf_ubs
        ~subst_only_local_vars:false
        ~subst_only_lps:only_lps
        ~subst_all:use_pos_jterm_final 
    end

let subst_pos_bounds pc cost_bounds only_lps =
  subst_pos_bounds_ pc cost_bounds only_lps false
  
let subst_pos_bounds_final pc cost_bounds =
  subst_pos_bounds_ pc cost_bounds false true

let subst_local_vars
      (pc:int)
      (cost_bounds: cost_bounds_t)
      (lmap: (jterm_t * cost_bound_t list) list)
      (umap: (jterm_t * cost_bound_t list) list):cost_bounds_t =
  
  (if !dbg then
     begin
       pr__debug [STR "subst_local_vars "; cost_bounds#toPretty; NL];
       pr__debug [STR "lmap = "; NL];
       List.iter (fun (jt, cs) ->
           pr__debug [jterm_to_pretty jt; STR ": "; pp_list cs; NL]) lmap;
       pr__debug [STR "umap = "; NL];
       List.iter (fun (jt, cs) ->
           pr__debug [jterm_to_pretty jt; STR ": "; pp_list cs; NL]) umap;
     end) ;
  
  if lmap = [] && umap = [] then
    cost_bounds
  else if is_const_range cost_bounds then
    cost_bounds
  else
    begin
      let (lbs, ubs, inf_lb, inf_ub) = get_bounds cost_bounds in
      let (lbs, ubs) = (lbs#toList, ubs#toList) in
      
      (if !dbg then
	begin
	  pr__debug [STR "lbs = "; pp_list lbs; NL];
	  pr__debug [STR "ubs = "; pp_list ubs; NL] 
	end) ;
      
      let new_lbs = List.filter (fun b -> b#is_local_var_linear) lbs in
      let new_ubs = List.filter (fun b -> b#is_local_var_linear) ubs in
      
      (if !dbg then
	begin
	  pr__debug [STR "new_lbs = "; pp_list new_lbs; NL];
	  pr__debug [STR "new_ubs = "; pp_list new_ubs; NL] 
	end) ;
      
      if List.length new_lbs < List.length lbs
         || List.length new_ubs < List.length ubs then
	begin
          
	  (if !dbg then
	     begin
	       pr__debug [STR "subst_local_vars lost precision";
                          cost_bounds#toPretty; NL];
	       pr__debug [STR "lmap: "; NL];
	       List.iter (fun (jt, ls) ->
                   pr__debug [jterm_to_pretty jt;
                              STR ": "; pp_list ls; NL]) lmap;
	       pr__debug [STR "umap: "; NL];
	       List.iter (fun (jt, ls) ->
                   pr__debug [jterm_to_pretty jt;
                              STR ": "; pp_list ls; NL]) umap
	    end)
	end ;
      
      let new_cost_bounds =
        new cost_bounds_t
            ~bottom:cost_bounds#isBottom
            ~simplify:false
            ~inflb:inf_lb
            ~infub:inf_ub
            ~lbounds:new_lbs
            ~ubounds:new_ubs in
      subst_in_cost_bounds
        ~pc
        ~cost_bounds:new_cost_bounds
        ~use_one_bound:true
        ~lmap
        ~umap
        ~inf_lbs:[]
        ~inf_ubs:[]
        ~subst_only_local_vars:true
        ~subst_only_lps:false
        ~subst_all:false
    end

let add_pos_jterm pc jterm (bounds: cost_bounds_t) =
  
  (if !dbg then
     pr__debug [STR "JCHCostBounds.add_jterm "; jterm_to_pretty jterm; NL;
                bounds#toPretty; NL]) ;
  
  pos_jterm_table#set jterm bounds ;
  let bounds_final = subst_pos_bounds_ pc bounds false true in
  pos_jterm_table_final#set jterm bounds_final

let add_pos_jterm_final pc jterm (bounds: cost_bounds_t) =
  let bounds_final = subst_pos_bounds_ pc bounds false true in
  pos_jterm_table_final#set jterm bounds_final ;
  bounds_final

let make_small_divs cost_bounds =
  
  (if !dbg then
     pr__debug [STR "make_small_divs "; NL; cost_bounds#toPretty; NL]) ;
  
  let res = 
    let (lbs, ubs, inf_lb, inf_ub) = get_bounds cost_bounds in
    let new_lbs = List.map (fun c -> c#make_small_div) lbs#toList in
    let new_ubs = List.map (fun c -> c#make_small_div) ubs#toList in
    new cost_bounds_t
        ~bottom:false
        ~simplify:false
        ~inflb:inf_lb
        ~infub:inf_ub
        ~lbounds:new_lbs
        ~ubounds:new_ubs in
  
  (if !dbg then
     pr__debug [STR "make_small_divs res "; NL; res#toPretty; NL]) ;
  
  res
  

let find_const_lb (for_lbs: bool) cost_bounds =
  
  (if !dbg then
    pr_debug [STR "find_const_lb "; pp_bool for_lbs ; NL;
              cost_bounds#toPretty; NL]) ;
  
  let (lbs, ubs, _, _) = get_bounds cost_bounds in
  let bs = if for_lbs then lbs else ubs in
  let const_lb = ref None in
  let check_lb lb =
    match (lb#find_const_lb, !const_lb) with
    | (Some (n, d), Some (lb, ld)) ->
       if (n#mult ld)#lt (lb#mult d) then
         const_lb := Some (n, d)
    | (Some (n, d), _) -> const_lb := Some (n, d)
    | (None, _) -> const_lb := None in
  List.iter check_lb bs#toList ;
  match !const_lb with
  | Some (n, d) -> n#modulo d
  | None -> numerical_zero 

let mk_from_poly index_map poly inf_ub =
  
  (if !dbg then
     pr__debug [STR "mk_from_poly "; NL]) ;
  
  if poly#is_bottom then
    bottom_cost_bounds
  else
    begin
      let constrs = poly#get_constraints in
      let poly_index_map = poly#get_index_map in
      
      (if !dbg then
        pr__debug [STR "poly_index_map = ";
                   pp_assoc_list_ints poly_index_map; NL]) ;
      
      (if !dbg then
         pr__debug [STR "index_map = ";
                    pp_list_int (List.map fst index_map);
                    STR " "; pp_list (List.map snd index_map); NL]) ;
      
      let eq_constrs = List.filter (fun c -> c#is_const_equality) constrs in
      let eq_inds = ref [] in
      let new_index_map = ref index_map in
      let add_eq (constr: JCHLinearConstraint.linear_constraint_t) =
        
	(if !dbg then
           pr__debug [STR "add_eq "; constr#toPretty; NL]) ;
        
	let (pairs, _) = constr#get_pairs_const in
	let (ind, _) = List.hd pairs in
	if ind != 0 then
	  begin
            
	    (if !dbg then
               pr__debug [STR "ind = "; INT ind; NL]) ;
            
	    eq_inds := ind :: !eq_inds ;
	    new_index_map := List.filter (fun (i, _) -> i != ind) !new_index_map
	  end in
      List.iter add_eq eq_constrs ;
      let res_poly = poly#project_out !eq_inds in
      let constrs = res_poly#get_constraints in
      let bounds =
        List.concat
          (List.map (bounds_from_linear_constraint !new_index_map) constrs) in
      let (lbs, ubs) = List.partition (fun b -> b#is_lb) bounds in
      if inf_ub then
        new cost_bounds_t
            ~bottom:false
            ~simplify:false
            ~inflb:false
            ~infub:true
            ~lbounds:lbs
            ~ubounds:[] 
      else
        new cost_bounds_t
            ~bottom:false
            ~simplify:false
            ~inflb:false
            ~infub:false
            ~lbounds:lbs
            ~ubounds:ubs
    end

(* join strategy *)
let rec join_stages (lbs1, ubs1, stage1) (lbs2, ubs2, stage2) new_inf_ub =
  
  (if !dbg then
     pr__debug [STR "join_stages "; INT stage1; STR " "; INT stage2; NL;
                pp_list ubs1; NL; pp_list ubs1; NL]) ;
  
    let index_map = make_index_map [lbs1; ubs1; lbs2; ubs2] in
    let make_lin_constrs map =
      let var_constrs = ref [] in
      let make_lin_constr (i, term) = 
	if List.for_all (fun jt -> is_pos_jterm jt) term#listOfKeys then 
	  var_constrs :=
            (new JCHLinearConstraint.linear_constraint_t
                 false [(i, unit_big_int)] zero_big_int) :: !var_constrs in
      begin
        List.iter make_lin_constr map ;
        !var_constrs
      end in
      
    (* make polys first. If this runs into trouble, then some constraints 
     * are changed or eliminated *)

    let var_constrs = make_lin_constrs index_map in

    let (poly1, _, new_lbs1, new_ubs1, new_stage1) =
      mk_poly stage1 lbs1 ubs1 var_constrs in
    let (poly2, _, new_lbs2, new_ubs2, new_stage2) =
      mk_poly stage2 lbs2 ubs2 var_constrs in

    (* Start from the beginning, with fewer constraints and variables. mk_poly 
     * is guaranteed to work for both constrs1 ans constrs2 *)

    let new_index_map = make_index_map [new_lbs1; new_ubs1; new_lbs2; new_ubs2] in
    let new_var_constrs = make_lin_constrs new_index_map in

    let constrs1 =
      List.rev_append
        (get_linear_constraint_list index_map lbs1 ubs1) new_var_constrs in
    
    (if !dbg then
       pr__debug [STR "constrs1 = "; pp_list constrs1; NL]) ;
    
    let constrs2 =
      List.rev_append
        (get_linear_constraint_list index_map lbs2 ubs2) new_var_constrs in
    
    (if !dbg then
       pr__debug [STR "constrs2 = "; pp_list constrs2; NL]) ;

    let poly1 = JCHPoly.mk_poly_from_constraints true constrs1 in
    let poly2 = JCHPoly.mk_poly_from_constraints true constrs2 in
    try
      let join_poly = poly1#join poly2 in
      mk_from_poly new_index_map join_poly new_inf_ub
    with _ -> 
      if stage1 = stage2 then
	if stage1 = 3 then
          mk_from_poly new_index_map JCHPoly.top_poly new_inf_ub 
	else
          join_stages
            (new_lbs1, new_ubs1, new_stage1)
            (new_lbs2, new_ubs2, new_stage2 - 1)
            new_inf_ub
      else if stage1 < stage2 then
	join_stages
          (new_lbs1, new_ubs1, new_stage1)
          (new_lbs2, new_ubs2, new_stage2 - 1)
          new_inf_ub
      else
	join_stages
          (new_lbs1, new_ubs1, new_stage1 - 1)
          (new_lbs2, new_ubs2, new_stage2)
          new_inf_ub

(* a join that does not depend on the assumptions for the JCHCostBounds.join *)
    let full_join cost_bounds1 cost_bounds2 =
      
      (if !dbg then
         pr__debug [STR "full_join "; cost_bounds1#toPretty; NL;
                    cost_bounds2#toPretty; NL]) ;
      
  let (lbs1, ubs1, inf_lb1, inf_ub1) = get_bounds cost_bounds1 in
  let (lbs2, ubs2, inf_lb2, inf_ub2) = get_bounds cost_bounds2 in
  match (cost_bounds1#isBottom,
         cost_bounds2#isBottom,
         cost_bounds1#isTop,
         cost_bounds2#isTop,
         inf_lb1,
         inf_lb2) with
    | (true, _, _, _, _, _) -> cost_bounds2
      | (_, true, _, _, _, _) -> cost_bounds1
      | (false, false, true, _, _, _)
      | (false, false, _, true, _, _) ->  top_cost_bounds
      | (false, false, false, false, true, _)
      | (false, false, false, false, _, true) -> inf_lb_cost_bounds
      | (false, false, false, false, fals, false) ->
	  let new_inf_ub = inf_ub1 || inf_ub2 in

	  let (lbs1, ubs1, lbs2, ubs2) =
	    if new_inf_ub then (lbs1#toList, [], lbs2#toList, [])
            else (lbs1#toList, ubs1#toList, lbs2#toList, ubs2#toList) in

	  let is_simple bs =
	    let is_simple_b b = b#has_pos_coeffs && b#has_pos_jterms in
	    List.length bs = 1 && is_simple_b (List.hd bs) in
  
	  if is_simple lbs1
             && is_simple lbs2
             && is_simple ubs1
             && is_simple ubs2 then
            cost_bounds1#join cost_bounds2
	  else 
	    begin
	      let join_cost =
                join_stages (lbs1, ubs1, 0) (lbs2, ubs2, 0) new_inf_ub in 
	      pr__debug [STR "full_join "; cost_bounds1#toPretty; STR " ";
                         cost_bounds2#toPretty; NL;
			 STR "full_join res = "; join_cost#toPretty; NL] ;
	      join_cost
	    end

let costbounds_to_string (cbounds:cost_bounds_t):string =
    let _ = cbounds#kind in
    let (lbs, ubs, inflbs, infubs) = get_st_bounds () in
    let cbcollection_to_string
          (cb_collection:JCHCostBound.CostBoundCollections.set_t):string =
        match cb_collection#singleton with
        | None -> "Sym"
        | Some cbound -> cost_bound_to_string cbound in
    let (lbs_string, ubs_string) =
      (cbcollection_to_string lbs, cbcollection_to_string ubs) in
    "(" ^ lbs_string ^ " , " ^ ubs_string ^ ")"	    

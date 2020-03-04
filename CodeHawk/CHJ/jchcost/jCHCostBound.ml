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

(* chlib *)
open CHExternalValues
open CHPretty
open CHNumerical
open CHLanguage

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHJTDictionary
open JCHJTerm

(* jchsys *)
open JCHPrintUtils

(* jchcost *)
open JCHCostUtils

let dbg = ref false

(* cost <= (sum terms) + const / div  or  cost => (sum terms) + const / div 
 * each term is of the form coeff x jterm1 ^ n1 x jterm ^ n2 x ...
 * div is pos *)
   
let max_small_coeff = mkNumerical 100
let max_small_div = mkNumerical 100
    
class cost_bound_t
        (is_lb: bool)
        (terms: numerical_t JTermTableCollections.table_t)
        (const: numerical_t)
        (div: numerical_t) =
object (self : 'a)
  val is_lb = is_lb
  val terms = ref terms
  val const = ref const
  val div = ref div

  val cost_var =
    let name = new symbol_t ~atts:["num"] "$cost$" in
    new variable_t name NUM_VAR_TYPE

  method is_lb = is_lb
  method get_div = !div
  method get_terms = !terms
  method get_term_pairs = !terms#listOfPairs
  method get_const = !const

  method private make_cost_bound is_lb terms const div =
    {< is_lb = is_lb;
      terms = ref terms;
      const = ref const;
      div = ref div >}

  method compare (bound: 'a) =
    let comp_div = !div#compare bound#get_div in
    if comp_div = 0 then
      let comp_const = !const#compare bound#get_const in
      if comp_const = 0 then
	compare_tables (compare_tables jterm_compare compare_num) compare_num
	  !terms bound#get_terms
      else
        comp_const
    else
      comp_div

  method is_const =
    !terms#size = 0     

  method is_pos_const =
    !terms#size = 0 && !const#geq numerical_zero

  method is_zero_const =
    !terms#size = 0 && !const#equal numerical_zero

  method is_non_0_const =
    !terms#size = 0 && not (!const#equal numerical_zero)

  method has_negative_coefficient =
    List.exists (fun (t,n) -> n#lt numerical_zero) !terms#listOfPairs

  method has_pos_jterms =
    List.for_all is_pos_jterm self#get_jterms#toList

  (* assume that the coeffs are pos *)
  method is_small =
    if !const#leq max_small_coeff then 
      List.for_all (fun n -> n#leq max_small_coeff) !terms#listOfValues
    else
      false

  method number_terms = !terms#size

  method private change_is_lb (a: 'a) = 
    {< is_lb = not a#is_lb;
      terms = ref a#get_terms;
      const = ref a#get_const;
      div = ref a#get_div >}

  method private find_index
      (index_map: (int * numerical_t JTermCollections.table_t) list)
      (t: numerical_t JTermCollections.table_t) =
    try
      fst (List.find
	     (fun (_, j) -> (compare_tables jterm_compare compare_num) t j = 0) index_map)
    with
    | Not_found ->
       raise (JCH_failure
		(LBLOCK [ STR "term " ; t#toPretty; 
			  STR " not found in JCHCostBounds.cost_bound_t find_index" ]))
      
  method get_jterms =
    let set = new JTermCollections.set_t in
    let add_prod table = set#addList table#listOfKeys in
    begin
      List.iter add_prod !terms#listOfKeys ;
      set
    end

  method equal (a: 'a) =
    if !div#equal a#get_div && !const#equal a#get_const then 
      begin
	let prods =
          JTermTableCollections.set_of_list
            (!terms#listOfKeys @ a#get_terms#listOfKeys) in
	let check prod =
	  try
	    (Option.get
               (!terms#get prod))#equal (Option.get (a#get_terms#get prod))
	  with _ -> false in
	List.for_all check prods#toList
      end
    else
      false

  method private augment (bound: 'a) (num: numerical_t) =
    {< is_lb = bound#is_lb;    
      terms = ref (bound#get_terms#map (fun t -> t#mult num));
      const = ref (bound#get_const#mult num) ;
      div = ref (bound#get_div#mult num) >} 

  method make_opposite =
    {< is_lb = not is_lb >}

  method private add_same_div (b1: 'a) (b2: 'a) =
    let new_terms = b1#get_terms#clone in
    let add_pair t num = 
      match new_terms#get t with
      | Some n ->
	  let new_num = n#add num in
	  if new_num#equal numerical_zero then new_terms#remove t
	  else new_terms#set t new_num
      | _ -> new_terms#set t num in
    begin
      b2#get_terms#iter add_pair ;
      {<is_lb = b1#is_lb;
        terms = ref new_terms;
        const = ref (b1#get_const#add b2#get_const) ;
        div = ref b1#get_div >}
    end
    
  method add (a: 'a) =
    if self#is_zero_const then a
    else if a#is_zero_const then
      self
    else if is_lb != a#is_lb then
      begin
	pr_debug [STR "adding a lower bound and an upper bound in " ;
                  STR "JCHCostBounds.cost_bound_t add"]; 
	raise (JCH_failure
		 (LBLOCK [STR "adding a lower bound and an upper bound " ;
                          STR "in JCHCostBounds.cost_bound_t add"]))
      end
    else 
      let lcm = !div#lcm a#get_div in
      let bound = self#augment self (lcm#div !div) in
      let abound = self#augment a (lcm#div a#get_div) in
      self#add_same_div bound abound 

  method neg =
    {< is_lb = not is_lb;
      terms = ref (!terms#clone#map (fun c -> c#neg));
      const = ref !const#neg >}

  method sub (a: 'a) =
    self#add (a#neg)

(* We assume that we multiply two positive cost bounds
 * mult is also used when multiplying two cost_bound_t that are viewed as just 
 * expressions not bounds, for instance in bound_from_jterm *)
  method mult (a: 'a) =
    let mult_prods (t1: numerical_t JTermCollections.table_t)
	(t2: numerical_t JTermCollections.table_t) =
      let new_t = t1#clone in
      let add_power (jterm, num) =
	match new_t#get jterm with
	| Some n -> new_t#set jterm (n#add num)
	| _ -> new_t#set jterm num in
      List.iter add_power t2#listOfPairs ;
      new_t in
    let mult_terms (t1, n1) (t2, n2) = (mult_prods t1 t2, n1#mult n2) in
    let mult_by_term (t2, n2) =
      List.map
        (fun (t1, n1) -> mult_terms (t1, n1) (t2, n2)) !terms#listOfPairs in
    let pairs = List.concat (List.map mult_by_term a#get_term_pairs) in
    let pairs1 =
      if a#get_const#equal numerical_zero then []
      else (!terms#map (fun t -> t#mult a#get_const))#listOfPairs in
    let pairs2 =
      if !const#equal numerical_zero then []
      else (a#get_terms#map (fun t -> t#mult !const))#listOfPairs in
    let new_terms = new JTermTableCollections.table_t in
    let add_terms (t, n) =
      match new_terms#get t with
      | Some num ->
	  let new_num = num#add n in
	  if new_num#equal numerical_zero then
            new_terms#remove t
	  else
            new_terms#set t new_num
      | _ -> new_terms#set t n in
    begin
      List.iter add_terms pairs ;
      List.iter add_terms pairs1;
      List.iter add_terms pairs2;
      
      self#simplify_coeffs
        {< terms = ref new_terms ;
	   const = ref (!const#mult a#get_const);
	   div = ref (!div#mult a#get_div)>}
    end
    
  (* assume a is a pos const *)
  method div (a: 'a) =
    if not a#is_const then
      raise (JCH_failure (STR "expected div by const "))
    else
      let aconst = a#get_const in
      if aconst#equal numerical_zero then
        raise (JCH_failure (STR "division by 0"))
      else 
	let adiv = a#get_div in
	self#simplify_coeffs
	  {< terms = ref (!terms#clone#map (fun n -> n#mult adiv));
	     const = ref (!const#mult adiv);
	     div = ref (!div#mult aconst)
          >}

  method private simplify_coeffs (a:'a) =
    let gcd =
      ref (if a#get_const#equal numerical_zero then
             a#get_div
           else
             a#get_const#gcd a#get_div) in
    let check_coeff coeff =
      gcd := !gcd#gcd coeff in
    begin
      List.iter check_coeff a#get_terms#listOfValues ;
      if !gcd#equal numerical_one then
        a
      else
        {< is_lb = a#is_lb;
	   terms = ref (a#get_terms#map (fun c -> c#div !gcd));
	   const = ref (a#get_const#div !gcd);
	   div = ref (a#get_div#div !gcd)
        >}
    end

  method make_small_div =
    if !div#leq max_small_div then
      self
    else if self#has_pos_jterms then 
      begin
	let nrs = !const :: !terms#listOfValues in
	let min = ref !div in
	let check_nr n =
	  if not (n#equal numerical_zero) then 
	    let nabs = n#abs in
	    if nabs#lt !min then min := nabs in
	List.iter check_nr nrs ;
	let changed = ref (!min != !div) in
	let change down n =
	  let new_n =    
	    let md = n#modulo !min in
	    let n' = (n#sub md)#div !min in
	    if down || md#equal numerical_zero then n'
	    else n'#add numerical_one in
	    new_n in 
	let res =  
	  {< terms = ref (!terms#map (change is_lb));
	    const = ref (change is_lb !const) ;
	    div = ref (change (not is_lb) !div)  >} in
	if !changed then
	  begin
	    let pp =
              LBLOCK [STR "changed bound div in bound ";
                      self#toPretty; STR ", resulting in ";
                      res#toPretty; NL] in
	    chlog#add
              "cost loss of precision"
              (LBLOCK [STR (pretty_to_string pp)]) ;
	    pr__debug [STR "cost loss of precision "; pp] ;
	  end ;
	res 
      end
    else
      begin
        (if !dbg then
           pr_debug [STR "small div or make_small_div does not have pos terms";
                     NL; self#toPretty; NL ]);
        self
      end
	
  method private mk_constant (is_lb:bool) (n:numerical_t) =
    self#make_cost_bound
      is_lb (new JTermTableCollections.table_t) n numerical_one

  (* assume both bounds have pos terms
   * not leq does not imply geq *)
  method leq (a: 'a) =
    let aterms = a#get_terms in
    let adiv = a#get_div in
    if (!const#mult adiv)#gt (a#get_const#mult !div) then false
    else
      begin
	let larger_coeff (prod, coeff) =
	  match aterms#get prod with
	  | Some acoeff -> (coeff#mult adiv)#leq (acoeff#mult !div)
	  | _ -> true in
	List.for_all larger_coeff !terms#listOfPairs
      end

  method geq (a: 'a) =
    let adiv = a#get_div in
    if (!const#mult adiv)#lt (a#get_const#mult !div) then false
    else
      begin
	pr_debug [STR "geq: the const of "; self#toPretty;
                  STR " is larger than the const of "; a#toPretty; NL] ;
	let larger_coeff (prod, acoeff) =
	  match !terms#get prod with
	  | Some coeff -> (acoeff#mult !div)#leq (coeff#mult adiv)
	  | _ -> true in
	List.for_all larger_coeff a#get_term_pairs
      end

  method power bound p =
    let int_p = p#toInt in
    if int_p = 0 then self#mk_constant bound#is_lb numerical_one
    else
      begin
	let res = ref bound in
	for i = 2 to int_p do
	  res := !res#mult bound
	done ;
	!res
      end

  method private subst_power
                   (is_lb:bool)
                   ((jterm, power):jterm_t * numerical_t)
                   (map: (jterm_t * 'a) list)
                   (is_jterm_to_keep:(jterm_t -> bool)): 'a = 
    if is_jterm_to_keep jterm then
      let t = new JTermCollections.table_t in
      let table = new JTermTableCollections.table_t in
      begin
        table#set t numerical_one ;
        t#set jterm power ;
        {< is_lb = is_lb ;
	   terms = ref table ;
	   const = ref numerical_zero ;
	   div = ref numerical_one >}
      end
    else
      try (* not in the map *)
	let new_bound =
          snd (List.find (fun (j, _) -> jterm_compare j jterm = 0) map) in
	self#power new_bound power 
      with
      | _ ->
         begin
	   pr__debug [STR "unbounded_term in "; self#toPretty; NL] ;
	   raise (JCHBasicTypes.JCH_failure (STR "unbounded term"))
	 end

  method private subst_term
                   (is_lb:bool) 
                   ((prod, num):numerical_t JTermCollections.table_t * numerical_t)
                   (map:(jterm_t * 'a) list)
                   (is_jterm_to_keep:(jterm_t -> bool)): 'a =
    let bound =
      ref {< is_lb = is_lb; 
	     terms = ref (new JTermTableCollections.table_t);
	     const = ref num;
	     div = ref numerical_one >} in
    let mult_by_power (jterm, power) = 
      bound :=
        !bound#mult
         (self#subst_power is_lb (jterm, power) map is_jterm_to_keep) in
    begin
      List.iter mult_by_power prod#listOfPairs ;
      !bound
    end
      
  method private subst_
                   (a: 'a)
                   (map: (jterm_t * 'a) list)
                   (is_jterm_to_keep:(jterm_t -> bool)) =
    let term_bounds =
      List.map
        (fun (prod, num) ->
          self#subst_term a#is_lb (prod, num) map is_jterm_to_keep)
	!terms#listOfPairs in
    let bound0 = self#mk_constant a#is_lb a#get_const in
    let add_term_bound sum term_bound = sum#add term_bound in
    let sum = List.fold_left add_term_bound bound0 term_bounds in
    self#make_cost_bound
      sum#is_lb sum#get_terms sum#get_const (sum#get_div#mult !div)

  method has_only_jterms_to_keep (is_jterm_to_keep: jterm_t -> bool) = 
    let is_good table =
      List.for_all is_jterm_to_keep table#listOfKeys in
    List.for_all is_good !terms#listOfKeys

   (* assume that all coefficient are positive
    * assume that all the quantities are positive or that self is linear *)
  method subst
           (bound_map:((jterm_t * 'a) list list))
           (is_jterm_to_keep: jterm_t -> bool) : 'a list =
    let all_jterms_are_keepers =
      List.for_all is_jterm_to_keep self#get_jterms#toList in
    if all_jterms_are_keepers then
      [self]
    else
      begin
	let bounds = ref [] in
	let add_bound map =
	  try
	    let bound = self#subst_ self map is_jterm_to_keep in
	    bounds := bound :: !bounds
	  with _ -> () in
	List.iter add_bound bound_map;
	!bounds
      end

   (* assume all coefficients are positive *)
  method simple_join (a: 'a) =
    let new_div = !div#lcm a#get_div in
    let mult = new_div#div !div in
    let amult = new_div#div a#get_div in

    let new_terms = new JTermTableCollections.table_t in
    let diff = new JTermTableCollections.table_t in
    let adiff = new JTermTableCollections.table_t in
    
    let set prod (n: numerical_t) (m: numerical_t) =
      let n = n#mult mult in
      let m = m#mult amult in
      if is_lb then
	if n#equal m then
	  new_terms#set prod n
	else if n#lt m then
	  begin
	    if n#gt numerical_zero then new_terms#set prod n ;
	    adiff#set prod (m#sub n) 
	  end
	else
	  begin
	    if m#gt numerical_zero then new_terms#set prod m;
	    diff#set prod (n#sub m)
	  end
      else
	if n#equal m then
	  new_terms#set prod n
	else if n#gt m then
	  begin
	    new_terms#set prod n;
	    adiff#set prod (n#sub m)
	  end
	else
	  begin
	    new_terms#set prod m;
	    diff#set prod (m#sub n)
	  end in
    
    let prods =
      JTermTableCollections.set_of_list
        (!terms#listOfKeys @ a#get_terms#listOfKeys) in
    
    let get_coeff
          (prod: numerical_t JTermCollections.table_t)
          (ts: numerical_t JTermTableCollections.table_t) = 
      match ts#get prod with Some n -> n | None -> numerical_zero in
    
    let add_prod prod =
      let c = get_coeff prod !terms in
      let ac = get_coeff prod a#get_terms in
      set prod c ac in

    prods#iter add_prod;

    let new_const = ref (!const#mult mult) in
    let new_aconst = ref (a#get_const#mult amult) in

    let diff_cost_bound =
      self#make_cost_bound is_lb diff numerical_zero numerical_one in
    let adiff_cost_bound =
      self#make_cost_bound is_lb adiff numerical_zero numerical_one in

    if is_lb then
      begin
	new_const :=
          !new_const#add (Option.get diff_cost_bound#find_const_lb_no_div) ;
	new_aconst :=
          !new_aconst#add (Option.get adiff_cost_bound#find_const_lb_no_div) ;	    
      end
    else
      begin
	new_const :=
          !new_const#sub (Option.get diff_cost_bound#find_const_lb_no_div) ;
	new_aconst :=
          !new_aconst#sub (Option.get adiff_cost_bound#find_const_lb_no_div) ;	    	
      end ;

    let new_const =
      if is_lb then
        if !new_const#leq !new_aconst then
          !new_const
        else
          !new_aconst
      else if !new_const#geq !new_aconst then
        !new_const
      else
        !new_aconst in

    let new_const =
      if new_const#lt numerical_zero then numerical_zero else new_const in

    let bound =     
      {< terms = ref new_terms;
	const = ref new_const;
	div = ref new_div >} in
    self#simplify_coeffs bound 

  method has_pos_coeffs =
    List.for_all (fun n -> n#geq numerical_zero) !terms#listOfValues

  method split_pos_neg =
    let pos_terms = new JTermTableCollections.table_t in
    let neg_terms = new JTermTableCollections.table_t in
    let check_coeff (prod, n) =
      if n#geq numerical_zero then
        pos_terms#set prod n
      else
        neg_terms#set prod n#neg in
    List.iter check_coeff !terms#listOfPairs ;
    let (pos_const, neg_const) =
      if !const#gt numerical_zero then
        (!const, numerical_zero)
      else
        (numerical_zero, !const#neg) in
    (self#make_cost_bound is_lb pos_terms pos_const !div,
     self#make_cost_bound (not is_lb) neg_terms neg_const !div)

  method private find_const_lb_term
                   ((prod, coeff):numerical_t JTermCollections.table_t * numerical_t) : numerical_t =
    let find_lb_jterm jterm =
      match jterm with
      | JConstant i 
      | JSymbolicConstant (_, Some i, _, _) -> i
      | JSize t -> numerical_zero
      | _ ->
	  begin
	    match JCHNumericAnalysis.get_pos_field_interval jterm with
	    | Some int -> int#getMin#toNumber
	    | _ ->
               raise
                 (JCH_failure
                    (LBLOCK [
                         STR "find_const_lb expected pos symbolic const, pos field, or size " ;
                         jterm_to_pretty jterm; NL])) 
	  end in
	  
	  
    let find_lb_power ((jterm, n): jterm_t * numerical_t) =
      let lb = find_lb_jterm jterm in
      let res = ref numerical_one in
      for i = 1 to n#toInt do
	res := !res#mult lb ;
      done;
      !res in
      
    let res = ref coeff in
    let mult_power p =
      res := !res#mult (find_lb_power p) in
    List.iter mult_power prod#listOfPairs ;
    !res 

  method find_const_lb_no_div =
    let find_lb_sum () = 
      let res = ref !const in
      let add_term t =
	res := !res#add (self#find_const_lb_term t) in
      List.iter add_term !terms#listOfPairs ;
      !res in
	
    if self#has_pos_jterms && self#has_pos_coeffs then
      try
	Some (find_lb_sum ())
      with _ -> None
    else
      None

  method find_const_lb =
    match self#find_const_lb_no_div with
    | Some n -> Some (n, !div)
    | _ -> None

(* used to make sure that a bound is safe to substitute into *)
  method is_local_var_linear =
    let is_linear (term, coeff) =
      let ps = term#listOfPairs in
      if (List.length ps) == 1 then 
	let (jt, power) = List.hd ps in
	power#equal numerical_one || not (is_local_var true jt)
      else
	begin
	  try
	    let n_local_vars = ref 0 in
	    let check_factor (jt, power) =
	      if power#equal numerical_one then
		(if is_local_var true jt then
                   incr n_local_vars)
	      else if is_local_var true jt then
                raise (JCH_failure (STR "")) in
	    List.iter check_factor ps;
	    if !n_local_vars >= 2 then
              false
	    else if !n_local_vars = 1 then
              coeff#gt numerical_zero
	    else
              true
	  with _ ->
	    if !dbg then pr__debug [STR "local_var^power"; NL] ;
	    false
	end in
    List.for_all is_linear !terms#listOfPairs

  method to_linear_constraint
      (index_map: (int * numerical_t JTermCollections.table_t) list) =
    let transform_pair (t, num) =
      (self#find_index index_map t,
       if is_lb then num#neg#getNum else num#getNum) in
    let cost_c = if is_lb then !div#getNum else !div#neg#getNum in
    let ps = (0, cost_c) :: (List.map transform_pair !terms#listOfPairs) in
    let cnst = if is_lb then !const#neg#getNum else !const#getNum in
    new JCHLinearConstraint.linear_constraint_t false ps cnst

  method to_jterm = 
    let prod_to_jterm t =
      let rec power_to_jterm power j n =
	if n = 0 then power
	else power_to_jterm (JArithmeticExpr (JTimes, power, j)) j (pred n) in
      let rec func pairs = 
	match pairs with
	| [(j, n)] -> power_to_jterm j j (pred n#toInt)
	| (j, n) :: rest_pairs ->
	    JArithmeticExpr (JTimes, power_to_jterm j j (pred n#toInt),
			     func rest_pairs)
	| _ -> raise (JCHBasicTypes.JCH_failure (STR "empty product")) in
      func t#listOfPairs in
	  
    let add_pair s (t, num) =
      if num#equal numerical_one then
	JArithmeticExpr (JPlus, s, prod_to_jterm t) 
      else
	JArithmeticExpr
          (JPlus, s, JArithmeticExpr (JTimes, JConstant num, prod_to_jterm t)) in
    let sum = List.fold_left add_pair (JConstant !const) !terms#listOfPairs in
    if !div#equal numerical_one then sum
    else JArithmeticExpr (JDivide, sum, JConstant !div)

  method write_xml node =
    jtdictionary#write_xml_jterm node self#to_jterm

  method toPretty =
    self#to_pretty_small 

  method to_string =
    let rel_str = if is_lb then " >= " else " <= " in
    rel_str ^ (jterm_to_string (self#to_jterm))

  method to_pretty_all =
    let pp_rel = STR (if is_lb then " >= " else " <= ") in
    let pp = jterm_to_pretty (self#to_jterm) in
    LBLOCK [pp_rel; pp]

  method to_pretty_small =
    let first = ref true in
    let pp_sign = if is_lb then STR ">= " else STR "<= " in
    let pp_jterm jterm =
      let rec pp_str jt = 
	match jt with
        (* TBA: JPower(t,n), JUninterpreted (name,terms) ?? *)
	| JLocalVar (-1) -> "return"
	| JLocalVar i -> "var"^(string_of_int i)
	| JAuxiliaryVar s -> s
        | JSymbolicConstant (_, lb_opt, _, name) ->
	    begin
	      match lb_opt with
	      | Some lb -> "sym_"^name^"("^(lb#toString)^")"
	      | _ -> "sym_"^name
	    end
	| JLoopCounter i -> "loop-counter@pc_" ^ (string_of_int i)
	| JStaticFieldValue (cnix,name) ->
	    ((JCHDictionary.retrieve_cn cnix)#name ^ "." ^ name)
	| JObjectFieldValue (cmsix,varix,cnix,name) ->
	    ((JCHDictionary.retrieve_cms cmsix)#name ^ ":var" ^ "." ^ name)
	| JConstant i -> i#toString
	| JBoolConstant b -> if b then "true" else "false"
	| JFloatConstant f -> string_of_float f
	| JStringConstant s -> s
	| JSize t -> "size(" ^ (pp_str t) ^ ")"
	| JUninterpreted (str, js) ->
	    let add_j (first, pp) j =
	      (false,
               if first then pp ^ (jterm_to_string j) else pp ^ ", "^(jterm_to_string j)) in
	    (snd (List.fold_left add_j (true, str ^ "(") js)) ^ ")" 
	| _ ->
           raise
             (JCH_failure (STR "unacceptable term in cost_bound_t")) in
      STR (pp_str jterm) in
    let pp_n n = n#toPretty in
    let terms_const :  ((jterm_t * numerical_t) list * numerical_t) list = 
      (List.map
         (fun (t, n) -> (t#listOfPairs, n)) !terms#listOfPairs) @ [([], !const)] in
    let pp_product
          (pp: pretty_t list)
          ((jterm, n): jterm_t * numerical_t):pretty_t list =
      if n#equal numerical_one then pp @ [STR "("; pp_jterm jterm; STR ")"]
      else pp @ [STR "("; pp_jterm jterm; STR ")^"; n#toPretty] in
    let rec pp_terms pp (t, n) =
      let pp_coeff c =
	if t = [] then [pp_n c]
	else if n#equal numerical_one then []
	else [pp_n c; STR " x "] in
      if n#equal numerical_zero && t = [] then pp
      else if n#geq numerical_zero then 
	begin
	  if !first then
	    begin
	      first := false;
	      List.fold_left pp_product ([pp_sign] @ (pp_coeff n)) t
	    end
	  else List.fold_left pp_product (pp @ [STR " + "] @ (pp_coeff n)) t
	end
      else
	begin
	  let n_abs = n#neg in
	  if !first then
	    begin
	      first := false;
	      List.fold_left pp_product ([pp_sign; STR "-"] @ (pp_coeff n_abs)) t
	    end
	  else List.fold_left pp_product (pp @ [STR " - "] @ (pp_coeff n_abs)) t
	end in
    let pp_sum = 
      if self#is_const then
        LBLOCK [pp_sign; pp_n !const]
      else
        LBLOCK (List.fold_left pp_terms [] terms_const) in
    if !div#equal numerical_one then
      pp_sum
    else
      LBLOCK [STR "("; pp_sum; STR ") / "; !div#toPretty] 
	
  method to_evx : external_value_exchange_format_t  =
    let is_lb_evx = EVX_STRING (if is_lb then "true" else "false") in
    let div_evx = EVX_STRING !div#toString in
    let pair_to_evx (table, num) =
      let power_to_evx (j, n) =
	EVX_LIST [EVX_STRING (jterm_to_string j);
		  EVX_STRING num#toString] in
      let powers_evx = EVX_LIST (List.map power_to_evx table#listOfPairs) in
      EVX_LIST [EVX_STRING num#toString; powers_evx] in
      
    let pairs_evx = EVX_LIST (List.map pair_to_evx !terms#listOfPairs) in
    let const_evx = EVX_STRING !const#toString in
    EVX_LIST [is_lb_evx; pairs_evx; const_evx; div_evx]
end

let cost_bound_from_num is_lb n =
  new cost_bound_t is_lb (new JTermTableCollections.table_t) n numerical_one
    
let bounds_from_linear_constraint
      index_map (constr: JCHLinearConstraint.linear_constraint_t) =
  let (ps, cnst) = constr#get_pairs_const in
  let div = ref numerical_zero in
  let terms = new JTermTableCollections.table_t in
  let transform_pair (i, n) =
    if i = 0 then
      div := mkNumerical_big n
    else
      terms#set (List.assoc i index_map) (mkNumerical_big n) in
  List.iter transform_pair ps ;
  if !div#equal numerical_zero then
    []
  else if !div#gt numerical_zero then
    let neg_terms = terms#map (fun n -> n#neg) in
    let neg_const = (mkNumerical_big cnst)#neg in
    if constr#is_equality then
      [new cost_bound_t true neg_terms neg_const !div;
	new cost_bound_t false neg_terms neg_const !div]
    else
      [new cost_bound_t true neg_terms neg_const !div]
  else
    let const = mkNumerical_big cnst in
    let neg_div = !div#neg in
    if constr#is_equality then
      [new cost_bound_t true terms const neg_div;
	new cost_bound_t false terms const neg_div]
    else
      [new cost_bound_t false terms const neg_div] 

let rec bound_from_jterm is_lb jterm : cost_bound_t =
  match jterm with
  (* TBA: JPower(t,n), JUninterpreted(name,terms) ?? *)
  | (JConstant n) ->
      let terms = new JTermTableCollections.table_t in
      new cost_bound_t is_lb terms n numerical_one
  | JSymbolicConstant _ ->
      let terms = new JTermTableCollections.table_t in
      let t = new JTermCollections.table_t in
      t#set jterm numerical_one ;
      terms#set t numerical_one ;
      new cost_bound_t is_lb terms numerical_zero numerical_one
  | JAuxiliaryVar _
  | JLocalVar _
  | JLoopCounter _
  | JStaticFieldValue _ 
  | JObjectFieldValue _
  | JSize _
  | JUninterpreted _ ->
      let terms = new JTermTableCollections.table_t in
      let t = new JTermCollections.table_t in
      t#set jterm numerical_one ;
      terms#set t numerical_one ;
      new cost_bound_t is_lb terms numerical_zero numerical_one
  | JPower (j, n) ->
      if n < 0 then
	raise (JCH_failure
                 (LBLOCK [STR "bound_from_jterm encountered negative power"; NL])) 
      else 
	begin
	  let c = bound_from_jterm is_lb j in
	  c#power c (mkNumerical n) 
	end
  | JArithmeticExpr (JTimes, j1, j2) ->
      let c1 = bound_from_jterm is_lb j1 in
      let c2 = bound_from_jterm is_lb j2 in
      c1#mult c2
  | JArithmeticExpr (JDivide, j1, j2) -> 
      let c1 = bound_from_jterm is_lb j1 in
      let c2 = bound_from_jterm is_lb j2 in
      c1#div c2
  | JArithmeticExpr (JPlus, j1, j2) ->
      let c1 = bound_from_jterm is_lb j1 in
      let c2 = bound_from_jterm is_lb j2 in
      c1#add c2
  | JArithmeticExpr (JMinus, j1, j2) ->
      let c1 = bound_from_jterm is_lb j1 in
      let c2 = bound_from_jterm (not is_lb) j2 in
      c1#sub c2      
  | _ -> raise Exit

let cost_bound_to_string (cbound:cost_bound_t):string =
	match cbound#is_const with
	| false -> "Sym"
	| true -> cbound#get_const#toString

module CostBoundCollections = CHCollections.Make 
    (struct
      type t = cost_bound_t
      let compare b1 b2 = b1#compare b2
      let toPretty b = b#toPretty
    end
)

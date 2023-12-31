(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHBounds
open CHCommon
open CHIntervals
open CHNumerical
open CHPEPRBounds
open CHPEPRTypes
open CHPretty


let trace_unary (indent:int) (name:string) arg1 result =
  pr_trace 3 [ INDENT (indent,
                       LBLOCK [ STR name ; STR " " ; arg1#toPretty ; STR " --> " ;
                                result#toPretty ; NL ]) ]
  
let trace_binary (indent:int) (name:string) arg1 (op:string) arg2 result =
  pr_trace 3[ INDENT (indent,
                      LBLOCK [ STR name ; STR " " ; arg1#toPretty ; STR op ; arg2#toPretty ;
                               STR " --> " ; result#toPretty ; NL ]) ]
  
let trace_binary_bool (indent:int) (name:string) arg1 (op:string) arg2 (result:bool) =
  pr_trace 3 [ INDENT (indent,
                       LBLOCK [ STR name ; STR " " ; arg1#toPretty ; STR op ; arg2#toPretty ;
                                STR " --> " ;
                                STR (if result then "true" else "false") ; NL ]) ]


class pepr_range_t (min_b:pepr_bound_int) (max_b:pepr_bound_int):pepr_range_int =
object (self:'a)

  val min = min_b
  val max = max_b
  val bottom = (max_b#disjoint min_b) 

  method get_min = min
  method get_max:pepr_bound_int = max

  method is_bottom = bottom

  method is_top =
    match (min#get_bound,max#get_bound) with
    | (XTOP,XTOP) -> true
    | _ -> false

  method is_bounded = not self#is_top && not self#is_bottom

  method equal (a:'a) =
    match (bottom, a#is_bottom) with
    | (true, true) -> true
    | (false, false) ->
       (match (self#is_top, a#is_top) with
       | (true, true) -> true
       | (false,false) -> min#equal a#get_min && max#equal a#get_max
       | _ -> false)
    | _ -> false

  method leq (a:'a) =
    let r =
      match (bottom, a#is_bottom) with
      | (true, _) -> true
      | (_, true) -> false
      | _ ->
         match (self#is_top, a#is_top) with
         | (_, true) -> true
         | (true,_) -> false
         | _ -> min#leq a#get_min && max#leq a#get_max in
    let _ = trace_binary_bool 1 "Range#leq" self " leq " a r in
    r
              
  method meet (a:'a) =
    let r = 
      match (bottom, a#is_bottom) with
      | (true, _) | (_, true) -> self#mkBottom
      | _ ->
         match (self#is_top, a#is_top) with
         | (true,_) -> a
         | (_, true) -> self
         | _ ->
            if (min#index = a#get_min#index) && (max#index = a#get_max#index) then
              self
            else
              self#mkNew  "meet" (min#meet a#get_min) (max#meet a#get_max) in
    let _ = trace_binary 1 "Range#meet" self " meet " a r in
    r

  method join (a:'a) =
    let r =
      match (bottom, a#is_bottom) with
      | (true,_) -> a
      | (_,true) -> self
      | _ ->
         match (self#is_top, a#is_top) with
         | (true,_) | (_, true) -> self#mkTop
         | _ ->
            if (min#index = a#get_min#index) && (max#index = a#get_max#index) then
              self
            else
              self#mkNew "join" (min#join a#get_min) (max#join a#get_max) in
    let _ = trace_binary 1 "Range#join" self " join " a r in
    r

  method widening (a:'a) =
    let r = 
      match (bottom, a#is_bottom) with
      | (true, _) -> self#mkBottom
      | (_, true) -> self
      | _ ->
         match (self#is_top, a#is_top) with
         | (true,_) -> self
         | (_, true) -> a
         | _ ->
            let lb = min#widening a#get_min in
            let ub = max#widening a#get_max in
            self#mkNew "widening" lb ub in
    let _ = trace_binary 1 "Range#widening" self " widening " a r in
    r

  method narrowing (a:'a) =
    let r = self#meet a in
    let _ = trace_binary 1 "Range#narrowing" self " narrowing " a r in
    r

  method lower_bound (b:pepr_bound_int) =
    let r =
      match b#get_bound with
      | XPSET _ -> self#strip (self#meet (self#mkNew "lower-bound" b xtop_pepr_bound))
      | _ -> ({< >}, mk_param_constraint_set []) in 
    let _ = trace_binary 1 "Range#lower_bound" self " lower-bound " b (fst r) in
    r

  method strict_lower_bound (b:pepr_bound_int) =
    let r = self#lower_bound (b#add (mk_number_pepr_bound_lb numerical_one)) in
    let _ = trace_binary 1 "Range#strict_lower_bound" self " strict-lower-bound" b (fst r) in
    r

  method upper_bound (b:pepr_bound_int) =
    let r =
      match b#get_bound with
      | XPSET _ -> self#strip (self#meet (self#mkNew "upper-bound" xtop_pepr_bound b))
      | _ -> ({< >}, mk_param_constraint_set []) in
    let _ = trace_binary 1 "Range#upper_bound" self " upper-bound " b (fst r) in
    r

  method strict_upper_bound (b:pepr_bound_int) =
    let r = self#upper_bound (b#add (mk_number_pepr_bound_ub numerical_one#neg)) in
    let _ = trace_binary 1 "Range#strict_upper_bound" self "upper-bound" b (fst r) in
    r
         
  method neg =
    let r = 
      if self#is_bottom || self#is_top then
        self
      else
        self#mkNew "neg" max#neg min#neg in
    let _ = trace_unary 1 "Range#neg" self r in
    r
    
  method add (a:'a) =
    let r = 
      match (bottom, a#is_bottom) with
      | (true,_) | (_, true) -> self#mkBottom
      | _ ->
         match (self#is_top, a#is_top) with
         | (true, _) | (_, true) -> self#mkTop
         | _ ->
            self#mkNew "add" (min#add a#get_min) (max#add a#get_max) in
    let _ = trace_binary 1 "Range#add" self " plus " a r in
    r

  method sub (a:'a) =
    let r = self#add a#neg in
    let _ = trace_binary 1 "Range#sub" self " minus " a r in
    r

  method mult (a:'a) =
    let r =
      match (bottom, self#is_bottom) with
      | (true,_) | (_, true) -> self#mkBottom
      | _ ->
         match self#singleton with
         | Some n -> a#multc n
         | _ ->
            match a#singleton with
            | Some n -> self#multc n
            | _ -> self#mkTop in
    let _ = trace_binary 1 "Range#mult" self " mult " a r in
    r

  method div (a:'a) =
    let r = self#mkTop in
    let _ = trace_binary 1 "Range#div" self " div " a r in
    r

  method multc (n:numerical_t) =
    if n#is_zero then
      self#mkZero
    else if n#gt numerical_zero then
      self#mkNew "multc" (min#multc n) (max#multc n)
    else
      self#mkTop
    (*  TBD
      self#mkNew "multc" (max#multc n) (min#multc n)    *)

  method singleton =
    if bottom || self#is_top then
      None
    else
      match (min#is_number, max#is_number) with
      | (true, true) when min#get_number#equal max#get_number ->
         Some min#get_number
      | _ -> None

  method parameters =
    if bottom || self#is_top then
      []
    else
      let min_i = min#get_parameter_indices in
      let max_i = max#get_parameter_indices in
      List.fold_left (fun acc i ->
          if List.exists (fun i' -> i = i') max_i then i::acc else acc) [] min_i

  method interval =
    if bottom || self#is_top then
      None
    else
      if min#is_number && max#is_number then
        Some (mkInterval min#get_number max#get_number)
      else
        None

  method parameter_exprs =
    if bottom || self#is_top then
      []
    else
      let minxprs = List.map (fun x -> (x#get_k, x#get_n)) min#get_parameter_exprs in
      let maxxprs = List.map (fun x -> (x#get_k, x#get_n)) max#get_parameter_exprs in
      List.fold_left (fun acc (k,n) ->
          if List.exists (fun (k',n') -> k#equal k' && n#equal n') maxxprs then
            (k,n) :: acc
          else
            acc) [] minxprs

  method remove_singleton (n:numerical_t) =
    let pex_lb = mk_number_pex_lb n in
    let pex_ub = mk_number_pex_ub n in
    self#mkNew "remove-singleton" (min#remove_pex pex_lb) (max#remove_pex pex_ub)

  method remove_interval (i:interval_t) =
    let errormsg = LBLOCK [ STR "Attempt to remove unbounded interval from symbolic range: " ;
                            i#toPretty ] in
    let pex_lb =
      match i#getMin#getBound with
      | NUMBER n -> mk_number_pex_lb n
      | _ -> raise (CHFailure errormsg) in
    let pex_ub =
      match i#getMax#getBound with
      | NUMBER n -> mk_number_pex_ub n
      | _ -> raise (CHFailure errormsg) in
    self#mkNew "remove-interval" (min#remove_pex pex_lb) (max#remove_pex pex_ub)

  method remove_equality (k:coeff_vector_int) (n:numerical_t) =
    let pex_lb = mk_pex k n LB in
    let pex_ub = mk_pex k n UB in
    self#mkNew "remove-equality" (min#remove_pex pex_lb) (max#remove_pex pex_ub)
    
  method toPretty =
    if bottom then
      STR "_|_"
    else
      LBLOCK [ STR "[" ;  min#toPretty ; STR " ; " ; max#toPretty ; STR "]" ]

  method private mkBottom = {< bottom = true >}

  method private mkTop = {< min = xtop_pepr_bound ; max = xtop_pepr_bound >}

  method private mkZero = self#mkSingleton numerical_zero

  method private mkSingleton n =
    let lb = mk_number_pepr_bound_lb n in
    let ub = mk_number_pepr_bound_ub n in
    self#mkNew "mkSingleton" lb ub

  method private mkNew (name:string) (l:pepr_bound_int) (u:pepr_bound_int) =
    let bottom = (u#disjoint l) in
    let _ = if bottom then
              pr_trace 3 [ STR "mkNew " ; l#toPretty ; STR " and " ; u#toPretty ;
                           STR " lead to bottom in " ; STR name ; NL ] in
    {< bottom = bottom ; min = l ; max = u >}

  method private strip (r:'a):('a * param_constraint_set_int) =
    let xprs = r#parameter_exprs in
    match xprs with
    | [] -> (r,mk_param_constraint_set [])
    | (k,n)::_ ->
       let (l',ldeps) = r#get_min#strip_dependencies (mk_pex k n LB) in
       let (u',udeps) = r#get_max#strip_dependencies (mk_pex k n UB) in
       let deps = mk_param_constraint_set (ldeps @ udeps) in
       let r = self#mkNew "strip" l' u' in
       let _ = pr_trace 2 [ STR "Transform " ; self#toPretty ; STR " with new bounds " ;
                            l'#toPretty ; STR " and " ; u'#toPretty ; STR " into " ;
                            r#toPretty ; STR " with dependencies " ;
                            deps#toPretty ; NL ] in
       (r,deps)

end

             
let mk_parameter_pepr_range (index:int) (size:int) =
  let lb = mk_parameter_pepr_bound_lb index size in
  let ub = mk_parameter_pepr_bound_ub index size in
  new pepr_range_t lb ub

let mk_singleton_pepr_range (n:numerical_t) =
  let lb = mk_number_pepr_bound_lb n in
  let ub = mk_number_pepr_bound_ub n in
  new pepr_range_t lb ub

let top_pepr_range = new pepr_range_t xtop_pepr_bound xtop_pepr_bound

let bottom_pepr_range =
  let lb = mk_number_pepr_bound_lb numerical_one in
  let ub = mk_number_pepr_bound_ub numerical_zero in
  new pepr_range_t lb ub


class pepr_value_t (v:pepr_value_type_t):pepr_value_int =
object (self:'a)

  val v = v

  method get_value = v

  method index =
    match v with
    | PEPRDEP d -> d#index
    | _ -> raise (CHFailure (self#wrongtypeErrorMsg "index"))

  method get_min =
    match v with
    | PEPRTOP -> xtop_pepr_bound
    | PEPRANGE r -> r#get_min
    | PEPRDEP _d -> raise (CHFailure (self#wrongtypeErrorMsg "get_min"))

  method get_max =
    match v with
    | PEPRTOP -> xtop_pepr_bound
    | PEPRANGE r -> r#get_max
    | PEPRDEP _d -> raise (CHFailure (self#wrongtypeErrorMsg "get_max"))

  method is_top = match v with PEPRTOP -> true | _ -> false

  method is_bottom =
    match v with
    | PEPRTOP -> false
    | PEPRANGE r -> r#is_bottom
    | PEPRDEP d -> d#is_bottom

  method is_bounded =
      match v with
      | PEPRTOP -> false
      | PEPRANGE r -> r#is_bounded
      | PEPRDEP _d -> raise (CHFailure (self#wrongtypeErrorMsg "is_bounded"))

  method equal (a:'a) =
    match (self#is_top, a#is_top) with
    | (true, true) -> true
    | (true,_) | (_, true) -> false
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> r#equal r'
       | (PEPRDEP d, PEPRDEP d') -> d#equal d'
       | _ -> raise (CHFailure (self#mismatchErrorMsg "equal" a))

  method leq (a:'a) =
    match (self#is_top, a#is_top) with
    | (true, true) -> true
    | (true, _) -> false
    | (_, true) -> true
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> r#leq r'
       | (PEPRDEP d, PEPRDEP d') -> d#leq d'
       | _ -> raise (CHFailure (self#mismatchErrorMsg "leq" a))

  method join (a:'a) =
    match (self#is_top, a#is_top) with
    | (true,_) -> self
    | (_, true) -> a
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#join r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#join d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "join" a))

  method meet (a:'a) =
    match (self#is_top, a#is_top) with
    | (true, _) -> a
    | (_, true) -> self
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#meet r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#meet d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "meet" a))

  method widening (a:'a) =
    match (self#is_top, a#is_top) with
    | (true, _) -> self
    | (_, true) -> a
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#widening r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#widening d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "widening" a))
            
  method narrowing (a:'a) =
    match (self#is_top, a#is_top) with
    | (true, _) -> a
    | (_, true) -> self
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#narrowing r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#narrowing d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "narrowing" a))

  method neg  =
    match v with
    | PEPRTOP -> self
    | PEPRANGE r -> self#mkNew (PEPRANGE r#neg)
    | PEPRDEP d -> self#mkNew (PEPRDEP d#neg)

  method add (a:'a) =
    match (self#is_top, a#is_top) with
    | (true,_) | (_, true) -> self#mkNew PEPRTOP
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#add r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#add d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "add" a))

  method sub (a:'a) =
    match (self#is_top, a#is_top) with
    | (true,_) | (_, true) -> self#mkNew PEPRTOP
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#sub  r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#sub d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "sub" a))

  method mult (a:'a) =
    match (self#is_top, a#is_top) with
    | (true,_) | (_,true) -> self#mkNew PEPRTOP
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#mult r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#mult d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "mult" a))

  method multc (n:numerical_t) =
    match v with
    | PEPRTOP -> self
    | PEPRANGE r -> self#mkNew (PEPRANGE (r#multc n))
    | PEPRDEP _ -> self

  method div (a:'a) =
    match (self#is_top, a#is_top) with
    | (true,_) | (_,true) -> self#mkNew PEPRTOP
    | _ ->
       match (v, a#get_value) with
       | (PEPRANGE r, PEPRANGE r') -> self#mkNew (PEPRANGE (r#div r'))
       | (PEPRDEP d, PEPRDEP d') -> self#mkNew (PEPRDEP (d#div d'))
       | _ -> raise (CHFailure (self#mismatchErrorMsg "div" a))

  method lower_bound (b:pepr_bound_int) =
    if self#is_top then
      let (r', _) = top_pepr_range#lower_bound b in
      (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP top_param_constraint_set))
    else
      match v with
      | PEPRANGE r ->
         let (r',deps) = r#lower_bound b in
         (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP deps))
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "lower_bound"))

  method upper_bound (b:pepr_bound_int) =
    if self#is_top then
      let (r', _) = top_pepr_range#upper_bound b in
      (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP top_param_constraint_set))
    else
      match v with
      | PEPRANGE r ->
         let (r',deps) = r#upper_bound b in
         (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP deps))
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "upper_bound"))

  method strict_lower_bound (b:pepr_bound_int) =
    if self#is_top then
      let (r', _) = top_pepr_range#strict_lower_bound b in
      (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP top_param_constraint_set))
    else
      match v with
      | PEPRANGE r ->
         let (r',deps) = r#strict_lower_bound b in
         (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP deps))
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "strict_lower_bound"))

  method strict_upper_bound (b:pepr_bound_int) =
    if self#is_top then
      let (r', _) = top_pepr_range#strict_upper_bound b in
      (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP top_param_constraint_set))
    else
      match v with
      | PEPRANGE r ->
         let (r',deps) = r#strict_upper_bound b in
         (self#mkNew (PEPRANGE r'), self#mkNew (PEPRDEP deps))
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "strict_upper_bound"))

  method singleton =
    if self#is_top then
      None
    else
      match v with
      | PEPRANGE r -> r#singleton
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "singleton"))

  method interval =
    if self#is_top then
      None
    else
      match v with
      | PEPRANGE r -> r#interval
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "interval"))

  method parameters =
    if self#is_top then
      []
    else
      match v with
      | PEPRANGE r -> r#parameters
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "parameter"))
           
  method parameter_exprs =
    if self#is_top then
      []
    else
      match v with
      | PEPRANGE r -> r#parameter_exprs
      | _ -> raise (CHFailure (self#wrongtypeErrorMsg "parameter_exprs"))

  method toPretty =
    match v with
    | PEPRTOP -> STR "<TOP>"
    | PEPRANGE r -> r#toPretty
    | PEPRDEP d -> d#toPretty

  method private wrongtypeErrorMsg name =
    LBLOCK [ STR "Unexpected value for applying " ; STR name  ; STR " in pepr-value: " ;
             self#toPretty ]

  method private mismatchErrorMsg name (a:'a) =
    LBLOCK [ STR "Unexpected value for operation " ; STR name ; STR " with operands " ;
             self#toPretty ; STR " and " ; a#toPretty ]

  method private mkNew v' = {< v = v' >}
                          
end
       
let bottom_pepr_value = new pepr_value_t (PEPRANGE bottom_pepr_range)
let top_pepr_value = new pepr_value_t PEPRTOP
    
let mk_singleton_pepr_value n = new pepr_value_t (PEPRANGE (mk_singleton_pepr_range n))
let mk_parameter_pepr_value (index:int) (size:int) =
  new pepr_value_t (PEPRANGE (mk_parameter_pepr_range index size))
                                 
let mk_dependency_pepr_value d = new pepr_value_t (PEPRDEP d)

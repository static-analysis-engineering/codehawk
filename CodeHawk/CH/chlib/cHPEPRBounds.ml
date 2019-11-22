(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
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
open CHIntervals
open CHLanguage
open CHNumerical
open CHPEPRDictionary
open CHPEPRTypes
open CHPretty

module H = Hashtbl
module P = Pervasives

let pd = CHPEPRDictionary.pepr_dictionary

let trace_unary (indent:int) (name:string) arg1 result =
  pr_trace 3 [ INDENT (indent,
                       LBLOCK [ STR name ; arg1#toPretty ; STR " --> " ;
                                result#toPretty ; NL ]) ]
  
let trace_binary (indent:int) (name:string) arg1 (op:string) arg2 result =
  pr_trace 3 [ INDENT (indent,
                       LBLOCK [ STR name ; arg1#toPretty ; STR op ; arg2#toPretty ;
                                STR " --> " ; result#toPretty ; NL ]) ]
  
let trace_binary_bool (indent:int) (name:string) arg1 (op:string) arg2 (result:bool) =
  pr_trace 3 [ INDENT (indent,
                       LBLOCK [ STR name ; arg1#toPretty ; STR op ; arg2#toPretty ;
                                STR " --> " ;
                                STR (if result then "true" else "false") ; NL ]) ]

class pepr_param_t
        (v:variable_t) (lb:numerical_t option) (ub:numerical_t option):pepr_param_int =
object

  method get_variable = v
  method lb = lb
  method ub = ub
  method toPretty =
    LBLOCK [ v#toPretty ;
             (match (lb,ub) with
              | (Some lb, Some ub) ->
                 LBLOCK [ STR "  [" ; lb#toPretty ; STR " ; " ; ub#toPretty ; STR "]" ]
              | (Some lb,_) ->
                 LBLOCK [ STR "  [" ; lb#toPretty ; STR " ; ->" ]
              | (_, Some ub) ->
                 LBLOCK [ STR "  <- ; " ; ub#toPretty ; STR "]" ]
              | _ -> STR "") ]
end

class pepr_params_t (params:pepr_param_int list):pepr_params_int =
object (self)

  method get_params = params

  method size = List.length params

  method nth (n:int) =
    if (List.length params) >= n then
      List.nth params n
    else
      raise (CHFailure (LBLOCK [ STR "Request for param " ; INT n ; STR " failed; only " ;
                                 INT (List.length params) ; STR " parameters found" ]))

  method has_variable (v:variable_t) =
    List.exists (fun p -> p#get_variable#equal v) params

  method variable_index (v:variable_t) =
    if self#has_variable v then
      let rec aux l i =
        match l with
        | [] -> raise (CHFailure (LBLOCK [ STR "Internal error in pepr-params" ]))
        | p::tl -> if p#get_variable#equal v then i else aux tl (i+1) in
      aux params 0
    else
      raise (CHFailure (LBLOCK [ STR "Request for variable index for " ; v#toPretty ;
                                 STR " failed: variable not found" ]))

  method toPretty =
    LBLOCK (List.map (fun p -> LBLOCK [ p#toPretty ; NL ]) params)

end

let mk_pepr_params (vl:variable_t list) =
  new pepr_params_t (List.map (fun v -> new pepr_param_t v None None) vl)

let normalize_coefficients (k:numerical_t list) =
  if List.for_all (fun c -> c#equal numerical_zero) k then [] else k

class coeff_vector_t (index:int) (k:numerical_t list):coeff_vector_int =
object (self:'a)

  val index = index
  val k = k

  method index = index
  method compare (a:'a) = P.compare index a#index
  method get_k = k
                        
  method equal (a:'a) = index = a#index

  method neg = self#mkNew (List.map (fun c -> c#neg) k)

  method add (a:'a) =
    let k' = a#get_k in
    if (List.length k) = (List.length k') then
      self#mkNew (List.map2 (fun c c' -> c#add c') k k')
    else
      match (k,k') with
      | ([],_) -> a
      | (_,[]) -> self
      | _ ->
         raise (CHFailure (LBLOCK [ STR "Unexpected combination of coefficient vectors: " ;
                                    self#toPretty ; STR " and " ; a#toPretty ])) 
    
  method mult (n:numerical_t) =
    if n#is_zero then
      self#mkNew []
    else
      self#mkNew (List.map (fun c -> c#mult n) k)

  method private count_c =
    List.fold_left (fun acc c -> if c#is_zero then acc else acc+1) 0 k
    
  method is_zero = self#count_c = 0

  method is_unary =
    self#count_c = 1 && (List.exists (fun c -> c#equal numerical_one) k)

  method get_single_coefficient_index =
    if self#is_unary then
      let rec aux l i =
        match l with
        | [] ->
           raise (CHFailure (LBLOCK [ STR "Single coefficient index not found in: " ;
                                      self#toPretty ]))
        | h::tl when h#equal numerical_one -> i
        | _::tl -> aux tl (i+1) in
      aux k 0
    else
      raise (CHFailure (LBLOCK [ STR "Coefficient vector is not unary: " ; self#toPretty ]))

  method get_pairs =
    let (_,l) =
      List.fold_left (fun (i,l) c ->
          if c#is_zero then
            (i+1,l)
          else (i+1, (i,c)::l)) (0,[]) k in
    List.rev l
         

  method private mkNew k' =
    let k' = normalize_coefficients k' in
    let index' = pd#index_coefficients k' in
    {< index = index' ; k = k' >}

  method toPretty =
    LBLOCK [ pretty_print_list k (fun c -> c#toPretty) "[" "," "]:" ; INT index]
    
end

let mk_coeff_vector (k:numerical_t list) =
  let k = normalize_coefficients k in
  let index = pd#index_coefficients k in
  new coeff_vector_t index k

let mk_index_coeff_vector (index:int) (size:int) =
  let a = Array.make size numerical_zero in
  let _ = Array.set a index numerical_one in
  mk_coeff_vector (Array.to_list a)

let zero_coeff_vector = mk_coeff_vector []

class param_constraint_t
        (index:int)
        (k:coeff_vector_int)
        (n:numerical_t)
        (pt:param_dep_type_t):param_constraint_int =
object (self:'a)

  val index = index
  val k = k
  val n = n
  val pt = pt

  method index = index
  method get_n = n
  method get_k = k
  method get_pt = pt

  method compare (a:'a) = P.compare index a#index

  method equal (a:'a) = index = a#index

  method neg = self#mkNew k#neg n#neg pt

  method add (a:'a) = self#mkNew (k#add a#get_k) (n#add a#get_n) a#get_pt

  method toPretty =
    LBLOCK [ k#toPretty ; STR " + " ; n#toPretty ;
             STR (match pt with P_EQ -> " = 0 " | _ -> " >= 0 ") ]

  method private mkNew k' n' apt =
    let pt' = match apt with P_INEQ -> P_INEQ | _ -> pt in
    let index' = pd#index_param_constraint_data k' n' pt' in
    {< index = index' ; k = k' ; n = n' ; pt = pt' >}

end

let mk_pconstraint_ineq (k:coeff_vector_int) (n:numerical_t) =
  let index = pd#index_param_constraint_data k n P_INEQ in
  new param_constraint_t index k n P_INEQ

class param_constraint_set_t (index:int) (s:param_constraint_int list):param_constraint_set_int =
object (self:'a)

  val index = index
  val s = s

  method index = index
  method get_s = s
  method compare (a:'a) = P.compare index a#index
  method equal (a:'a) = index = a#index

  method leq (a:'a) =
    (index = a#index) ||
      (List.for_all (fun x' -> List.exists (fun x -> x#equal x') s) a#get_s)

  method is_top = (List.length s) = 0

  method is_bottom = false

  method join (a:'a) =
    if index = a#index then self else
      let s' =
        List.fold_left (fun acc x ->
            if List.exists (fun x' -> x#equal x') a#get_s then x :: acc else acc)
                       [] s in
      self#mkNew s'

  method meet (a:'a) =
    if index = a#index then self else
      let s' =
        List.fold_left
          (fun acc x -> if List.exists (fun x' -> x#equal x') acc then acc else x::acc)
          s a#get_s in
      self#mkNew s'

  method widening = self#join
  method narrowing = self#meet

  method neg = self#mkNew (List.map (fun x -> x#neg) s)

  method add (a:'a) = self#mkNew (self#x_product (fun x x' -> x#add x') s)

  method sub (a:'a) = self#add a#neg

  method mult (a:'a) = self#mkNew []

  method div (a:'a) = self#mkNew []

  method toPretty =
    LBLOCK [ pretty_print_list s (fun x -> x#toPretty) "[" "; " "]" ]
                        
  method private x_product f s' =
    List.fold_left (fun acc1 x ->
        List.fold_left (fun acc2 x' ->
            (f x x') :: acc2) acc1 s') [] s

  method private mkNew (s':param_constraint_int list) =
    let index' = pd#index_param_constraint_set_data s in
    {< index = index' ; s = s' >}

end

let mk_param_constraint_set (s:param_constraint_int list) =
  let index = pd#index_param_constraint_set_data s in
  new param_constraint_set_t index s

let top_param_constraint_set = mk_param_constraint_set []

class pex_t (index:int) (k:coeff_vector_int) (n:numerical_t) (bt:bound_type_t):pex_int =
object (self:'a)

  val index = index
  val k = k
  val n = n
  val bt = bt
        
  method index = index
  method get_n = n
  method get_k = k
  method get_bt = bt

  method compare (a:'a) = P.compare index a#index
  method equal (a:'a) = index = a#index

  method is_number = k#is_zero 

  method get_number =
    if k#is_zero then
      n
    else
      raise (CHFailure (self#errorMsg "number"))

  method is_parameter = k#is_unary && n#equal numerical_zero

  method get_parameter_index =
    if self#is_parameter then
      k#get_single_coefficient_index
    else
      raise (CHFailure (self#errorMsg "single expression"))

  method leq (a:'a) =
    let r =
      (k#equal a#get_k) &&
        (let n' = a#get_n in
         match bt with
         | LB -> n#geq n'
         | UB -> n#leq n') in
    let _ = trace_binary_bool 5 "Pex#leq" self " leq " a r in
    r

  method disjoint (a:'a) =
    let r = 
      let n' = a#get_n in
      (k#equal a#get_k) &&
        (match (bt, a#get_bt) with
         | (LB, UB) -> n#gt n'
         | (UB, LB) -> n#lt n'
         | _ -> false) in
    let _ = trace_binary_bool 5 "Pex#disjoint" self " disjoint " a r in
    r
           

  method neg =
    let r = self#mkNewBound k#neg n#neg in
    let _ = trace_unary 5 "Pex#neg" self r in
    r

  method add (a:'a) =
    if not (bt = a#get_bt) then
      raise (CHFailure (LBLOCK [ STR "Unexpected add of pex: " ; self#toPretty ;
                                 STR " with " ; a#toPretty ]))
    else
      let r = self#mkNew (k#add a#get_k) (n#add a#get_n) in
      let _ = trace_binary 5 "Pex#add" self " plus " a r in
      r

  method mult (m:numerical_t) =
    let r = self#mkNew (k#mult m) (n#mult m) in
    let _ = trace_binary 5 "Pex#mult" self " mult " m r in
    r

  method meet (a:'a) =
    if not (bt = a#get_bt) then
      raise (CHFailure (LBLOCK [ STR "Unexpected meet of pex: " ; self#toPretty ;
                                 STR " with " ; a#toPretty ]))
    else
      let r = 
        if k#equal a#get_k then
          let n' = a#get_n in
          match bt with
          | LB -> if n#gt n' then self else self#mkNew k n'
          | UB -> if n#lt n' then self else self#mkNew k n'
        else
          raise (CHFailure (LBLOCK [ STR "Unexpected meet of pex: " ; self#toPretty ;
                                     STR " with " ; a#toPretty ])) in
      let _ = trace_binary 5 "Pex#meet" self " meet " a r in
      r
      
  method join (a:'a) =
    if not (bt = a#get_bt) then
      raise (CHFailure (LBLOCK [ STR "Unexpected join of pex: " ; self#toPretty ;
                                 STR " with " ; a#toPretty ]))
    else
      let r =
        if k#equal a#get_k then
          let n' = a#get_n in
          match bt with
          | LB -> if n#lt n' then self else self#mkNew k n'
          | UB -> if n#gt n' then self else self#mkNew k n'
        else
          raise (CHFailure (LBLOCK [ STR "Unexpected join of pex: " ; self#toPretty ;
                                     STR " with " ; a#toPretty ])) in
      let _ = trace_binary 5 "Pex#join" self " join " a r in
      r
      
  method toPretty =
    LBLOCK [ STR (match bt with LB -> "LB:" | UB -> "UB:") ;
             k#toPretty ; STR ", " ; n#toPretty ]

  method private mkNew (k':coeff_vector_int) (n':numerical_t) =
    let index' = pd#index_pex_data k' n' bt in
    {< index = index'; k = k' ; n = n' >}

  method private mkNewBound (k':coeff_vector_int) (n':numerical_t) =
    let bt' = match bt with UB -> LB | LB -> UB in
    let index' = pd#index_pex_data k' n' bt' in
    {< index = index' ; k = k' ; n = n' ; bt = bt' >}

  method private errorMsg s =
    LBLOCK [ STR "Parametric epxression is not a " ; STR s ]

end

let mk_pex (k:coeff_vector_int) (n:numerical_t) (bt:bound_type_t) =
  let index = pd#index_pex_data k n bt in
  new pex_t index k n bt

let mk_number_pex_lb n = mk_pex zero_coeff_vector n LB
let mk_number_pex_ub n = mk_pex zero_coeff_vector n UB

let mk_parameter_pex (index:int) (size:int) (bt:bound_type_t) =
  let k = mk_index_coeff_vector index size in
  mk_pex k numerical_zero bt

let mk_parameter_pex_lb (index:int) (size:int) = mk_parameter_pex index size LB
let mk_parameter_pex_ub (index:int) (size:int) = mk_parameter_pex index size UB

let zero_pex_lb = mk_number_pex_lb numerical_zero
let zero_pex_ub = mk_number_pex_ub numerical_zero

(* combine instances with the same coefficient vector;
   throw an exception if the size exceeds 5 *)
let normalize_pex_list (s:pex_int list):pex_int list =
  let merge l =
    List.fold_left (fun acc x -> acc#meet x) (List.hd l) (List.tl l) in
  let t = H.create 3 in
  let _ = List.iter (fun x ->
              let kindex = x#get_k#index in
              let entry = if H.mem t kindex then H.find t kindex else [] in
              H.replace t kindex (x::entry)) s in
  let r = 
    List.sort
      (fun x x' -> P.compare x#index x'#index)
      (H.fold (fun _ v acc ->
           match v with
           | [] -> acc
           | [ x ] -> x::acc
           | _ -> (merge v) :: acc) t []) in
  if (List.length r) > 5 then
    raise (CHDomainFailure
             ("pepr",LBLOCK [ STR "conjunction: " ;
                              pretty_print_list r (fun x -> x#toPretty) "{" ", " "}" ]))
  else
    r
    
  
class pex_set_t (index:int) (s: pex_int list):pex_set_int =
object (self:'a)

  val index = index
  val s = s

  method index = index
  method get_s = s
        
  method compare (a:'a) = P.compare index a#index
  method equal (a:'a) = index = a#index

  method leq (a:'a) =
    let r =
      (index = a#index) ||
        (let s' = a#get_s in
         ((List.length s') <= (List.length s))
         && (List.fold_left (fun acc x' ->
                 acc && List.exists (fun x -> x#leq x') s) true s')) in
    let _ = trace_binary_bool 4 "Pexset#leq" self " leq "  a r in
    r

  method disjoint (a:'a) =
    let r =
      (let s' = a#get_s in
       List.fold_left (fun acc1 x ->
           acc1 || List.exists (fun x' -> x#disjoint x') s') false s) in
    let _ = trace_binary_bool 4 "Pexset#disjoint" self " disjoint " a r in
    r

  method is_top = match s with [] -> true | _ -> false

  method is_number = List.exists (fun x -> x#is_number) s

  method is_parameter = List.exists (fun x -> x#is_parameter) s

  method get_number =
    try
      let x = List.find (fun x -> x#is_number) s in x#get_number
    with
      Not_found -> raise (CHFailure (self#errorMsg "number"))

  method get_parameter_indices =
    List.map (fun x ->
        x#get_parameter_index) (List.filter (fun x -> x#is_parameter) s)

  method neg =
    let r = self#mkNew (List.map (fun x -> x#neg) s) in
    let _ = trace_unary 4 "Pexset#neg" self r in
    r

  method add (a:'a) =
    let r = self#mkNew (self#x_product (fun x x' -> x#add x') a#get_s) in
    let _ = trace_binary 4 "Pexset#add" self " plus " a r in
    r

  method mult (n:numerical_t) =
    let r = self#mkNew (List.map (fun x -> x#mult n) s) in
    let _ = trace_binary 4 "Pexset#mult" self " mult " n r in
    r

  method meet (a:'a) =
    let r = self#mkNew (s @ a#get_s) in
    let _ = trace_binary 4 "Pexset#meet" self " meet " a r in
    r

  method remove_pex (pex:pex_int) =
    if List.exists (fun x -> x#equal pex) s then
      self#mkNew (List.filter (fun x -> not (x#equal pex)) s)
    else
      raise (CHFailure (LBLOCK [ STR "Attempt to remove non-existing parametric expression: " ;
                                 pex#toPretty ; STR " from set " ; self#toPretty ]))

  method strip_dependencies (pex:pex_int) =
    if List.exists (fun x -> x#equal pex) s then
      let s' = self#mkNew [ pex ] in
      let deps =
        match pex#get_bt with
        | LB ->
           List.fold_left (fun acc x ->
               if x#equal pex then acc else
                 let pk = pex#get_k#add x#get_k#neg in
                 let pn = pex#get_n#add x#get_n#neg in
                 (mk_pconstraint_ineq pk pn) :: acc) [] s
        | UB ->
           List.fold_left (fun acc x ->
               if x#equal pex then acc else
                 let pk = x#get_k#add pex#get_k#neg in
                 let pn = x#get_n#add pex#get_n#neg in
                 (mk_pconstraint_ineq pk pn) :: acc) [] s in
      (s',deps)
    else
      raise (CHFailure (LBLOCK [ STR "Attempt to strip non-existing parametric expression: " ;
                                 pex#toPretty ; STR " in set " ; self#toPretty ]))

  method toPretty =
    LBLOCK [ pretty_print_list s (fun s -> s#toPretty) "[" " && " "]" ]
                                    
  method private x_product f s' =
    List.fold_left (fun acc1 x ->
        List.fold_left (fun acc2 x' ->
            (f x x') :: acc2) acc1 s') [] s
    
  method private mkNew s' =
    let s' = normalize_pex_list s' in
    let index' = pd#index_pex_set_data s' in
    {< index = index' ; s = s' >}

  method private errorMsg s =
    LBLOCK [ STR "Parametric expression set is not a " ; STR s ; STR ": " ;
             self#toPretty ; NL ]
end

let mk_pex_set (s:pex_int list) =
  let s = normalize_pex_list s in
  let index = pd#index_pex_set_data s in
  new pex_set_t index s

let top_pex_set = mk_pex_set []

let zero_pex_set_lb = mk_pex_set [ zero_pex_lb ]
let zero_pex_set_ub = mk_pex_set [ zero_pex_ub ]

let mk_number_pex_set_lb n = mk_pex_set [ mk_number_pex_lb n ]
let mk_number_pex_set_ub n = mk_pex_set [ mk_number_pex_ub n ]

let mk_parameter_pex_set_lb index size = mk_pex_set [ mk_parameter_pex_lb index size ]
let mk_parameter_pex_set_ub index size = mk_pex_set [ mk_parameter_pex_ub index size ]

let normalize_pex_set_list (p:pex_set_int list):pex_set_int list =
  if List.exists (fun s -> s#is_top) p then
    [ top_pex_set ]
  else
    let r =
      List.sort
        (fun s s' -> P.compare s#index s'#index)
        (List.fold_left (fun acc s ->
             if List.exists (fun s' -> s#index = s'#index) acc then
               acc
             else if List.exists (fun s' -> (not (s#equal s')) && s#leq s') p then
               acc
             else
               s :: acc) [] p) in
    if (List.length r) > 5 then
      raise (CHDomainFailure
               ("pepr",
                LBLOCK [ STR "disjunction: " ;
                         pretty_print_list p (fun s -> s#toPretty) "{" "; " "]" ]))
    else
      r

class pex_pset_t (index:int) (p:pex_set_int list):pex_pset_int =
object (self)

  val index = index
  val p = p

  method index = index
  method get_p = p

  method compare (a:'a) = P.compare index a#index
  method equal (a:'a) = index = a#index

  method leq (a:'a) =
    let r =
      (index = a#index) ||
        (let p' = a#get_p in
         ((List.length p) <= (List.length p'))
         && (List.fold_left (fun acc s ->
                 acc && List.exists (fun s' -> s#leq s') p') true p)) in
    let _ = trace_binary_bool 3 "PexPset#leq" self " leq " a r in
    r

  method disjoint (a:'a) =
    let r =
      (let p' = a#get_p in
       List.fold_left (fun acc s ->
           acc && (List.for_all (fun s' -> s#disjoint s') p')) true p) in
    let _ = trace_binary_bool 3 "PexPset#disjoint" self " disjoint " a r in
    r
      
  method neg =
    let r = self#mkNew (List.map (fun s -> s#neg) p) in
    let _ = trace_unary 3 "PexPset#neg" self r in
    r

  method add (a:'a) =
    let r = self#mkNew (self#x_product (fun s s' -> s#add s') a#get_p) in
    let _ = trace_binary 3 "PexPset#add" self " plus " a r in
    r

  method mult (n:numerical_t) =
    let r = self#mkNew (List.map (fun s -> s#mult n) p) in
    let _ = trace_binary 3 "PexPset#mult" self " mult " n r in
    r

  method join (a:'a) =
    let r = self#mkNew (p @ a#get_p) in
    let _ = trace_binary 3 "PexPset#join" self " join " a r in
    r

  method meet (a:'a) =
    let r = self#mkNew (self#x_product (fun s s' -> s#meet s') a#get_p) in
    let _ = trace_binary 3 "PexPset#meet" self " meet " a r in
    r

  method is_top = List.exists (fun s -> s#is_top) p

  method is_number = match p with [ s ] -> s#is_number | _ -> false

  method get_number =
    match p with
    | [ s ] -> s#get_number
    | _ -> raise (CHFailure (self#errorMsg "number"))

  method get_parameter_indices =
    match p with
    | [ s ] -> s#get_parameter_indices
    | _ -> []        (* TBD: extract common factors *)

  method get_parameter_exprs =
    match p with
    | [ s ] -> s#get_s
    | _ -> []        (* TBD: extract common factors *)
            
  method widening (a:'a) =
    let r =
      let p' = self#join a in
      if self#equal p' then
        self
      else
        self#mk_top in
    let _ = trace_binary 3 "PexPset#widening " self " widening " a r in
    r

  method remove_pex (pex:pex_int) =
    self#mkNew (List.map (fun s -> s#remove_pex pex) p)

  method strip_dependencies (pex:pex_int) =
    match p with
    | [ s ] ->
       let (s',deps) = s#strip_dependencies pex in
       (self#mkNew [ s' ], deps)
    | _ ->
       raise (CHFailure (LBLOCK [ STR "Attempt to strip dependencies from multiple alternatives" ]))

  method toPretty =
      LBLOCK [ pretty_print_list p (fun s -> s#toPretty) "[" " || " "]" ]

  method private x_product f p' =
    List.fold_left (fun acc1 s ->
        List.fold_left (fun acc2 s' ->
            (f s s') :: acc2) acc1 p') [] p

  method private mk_top = self#mkNew [ mk_pex_set [] ]

  method private mkNew p' =
    let p' = normalize_pex_set_list p' in
    let index' = pd#index_pex_pset_data p' in
    {< index = index'; p = p' >}

  method private errorMsg s =
    LBLOCK [ STR "Parametric expression powerset is not a " ; STR s ; STR ": " ;
             self#toPretty ]

end

let mk_pex_pset (p:pex_set_int list) =
  let p = normalize_pex_set_list p in
  let index = pd#index_pex_pset_data p in
  new pex_pset_t index p

let zero_pex_pset_lb = mk_pex_pset [ zero_pex_set_lb ]
let zero_pex_pset_ub = mk_pex_pset [ zero_pex_set_ub ]

let mk_number_pex_pset_lb n = mk_pex_pset [ mk_number_pex_set_lb n ]
let mk_number_pex_pset_ub n = mk_pex_pset [ mk_number_pex_set_ub n ]

let mk_parameter_pex_pset_lb index size =
  mk_pex_pset [ mk_parameter_pex_set_lb index size ]

let mk_parameter_pex_pset_ub index size =
  mk_pex_pset [ mk_parameter_pex_set_ub index size ]

let top_pex_pset = mk_pex_pset [ top_pex_set ]

let normalize_pepr_bound (b:pepr_bounds_t) =
  match b with
  | XTOP -> XTOP
  | XPSET p when List.exists (fun s ->
                     match s#get_s with [] -> true | _ -> false) p#get_p -> XTOP
  | _ -> b
  
class pepr_bound_t (index:int) (b:pepr_bounds_t):pepr_bound_int =
object (self:'a)

  val index = index
  val bound = b

  method index = index
  method get_bound = bound

  method is_top = match bound with XTOP -> true | _ -> false

  method is_number = match bound with XPSET p -> p#is_number | _ -> false

  method get_number =
    match bound with
    | XPSET p -> p#get_number
    | _ -> raise (CHFailure (self#errorMsg "number"))

  method get_parameter_indices =
    match bound with
    | XPSET p -> p#get_parameter_indices
    | _ -> []

  method get_parameter_exprs =
    match bound with
    | XPSET p -> p#get_parameter_exprs
    | _ -> []

  method equal (a:'a) = index = a#index
    
  method leq (a:'a) =
    let r =
      (index = a#index) ||
        (match (bound,a#get_bound) with
         | (_, XTOP) -> true
         | (XPSET p, XPSET p') -> p#leq p'
         | _ -> false) in
    let _ = trace_binary_bool 2 "Bound#leq" self " leq " a r in
    r

  method disjoint (a:'a) =
    let r =
      (match (bound,a#get_bound) with
       | (XTOP,_) | (_,XTOP) -> false
       | (XPSET p, XPSET p') -> p#disjoint p') in
    let _ = trace_binary_bool 2 "Bound#disjoint" self " disjoint " a r in
    r

  method neg =
    let r = 
      match bound with
      | XTOP -> self
      | XPSET p -> self#mkNew (XPSET p#neg) in
    let _ = trace_unary 2 "Bound#neg" self r in
    r

  method add (a:'a) =
    let r =
      match (bound, a#get_bound) with
      | (XTOP,_) | (_,XTOP) -> self#mkNew XTOP
      | (XPSET p, XPSET p') -> self#mkNew (XPSET (p#add p')) in
    let _ = trace_binary 2 "Bound#add" self " plus " a r in
    r

  method mult (a:'a) =
    let r =
      match (bound, a#get_bound) with
      | (XTOP,_) | (_, XTOP) -> self#mkNew XTOP
      | (XPSET p, XPSET p') when p#is_number -> self#mkNew (XPSET (p'#mult p#get_number))
      | (XPSET p, XPSET p') when p'#is_number -> self#mkNew (XPSET (p#mult p'#get_number))
      | (XPSET p, XPSET p') -> self#mkNew XTOP in
    let _ = trace_binary 2 "Bound#mult" self " mult " a r in
    r

  method multc (n:numerical_t) =
    match bound with
    | XTOP -> self
    | XPSET p -> self#mkNew (XPSET (p#mult n))

  method join (a:'a) =
    let r =
      if index = a#index then
        self
      else
        match (bound, a#get_bound) with
        | (XTOP, _) | (_, XTOP) -> self#mkNew XTOP
        | (XPSET p, XPSET p') -> self#mkNew (XPSET (p#join p')) in
    let _ = trace_binary 3 "Bound#join" self " join " a r in
    r

  method meet (a:'a) =
    let r =
      if index = a#index then
        self
      else
        match (bound, a#get_bound) with
        | (XTOP, _) -> a
        | (_, XTOP) -> self
        | (XPSET p, XPSET p') -> self#mkNew (XPSET (p#meet p')) in
    let _ = trace_binary 2 "Bound#meet" self " meet " a r in
    r

  method widening (a:'a) =
    let r = 
      match (bound, a#get_bound) with
      | (XTOP,_) -> self
      | (_, XTOP) -> a
      | (XPSET p, XPSET p') -> self#mkNew (XPSET (p#widening p')) in
    let _ = trace_binary 2 "Bound#widening" self " widening " a r in
    r

  method remove_pex (pex:pex_int) =
    match bound with
    | XTOP -> raise (CHFailure (STR "Attempt to remove parametric expression from top bound"))
    | XPSET p -> self#mkNew (XPSET (p#remove_pex pex))

  method strip_dependencies (pex:pex_int) =
    match bound with
    | XTOP -> raise (CHFailure (STR "Attempt to strip dependencies from top bound"))
    | XPSET p ->
       let (p',deps) = p#strip_dependencies pex in
       (self#mkNew (XPSET p'), deps)

  method toPretty =
    match bound with
    | XTOP -> STR "T"
    | XPSET p -> p#toPretty
 
  method private mkNew (b:pepr_bounds_t) =
    let b = normalize_pepr_bound b in
    let index' = pd#index_pepr_bound_data b in
    {< index = index' ; bound = b >}

  method private errorMsg s =
    LBLOCK [ STR "Parametric expression bound is not a " ; STR s ]

end

let xtop_pepr_bound =
  let index = pd#index_pepr_bound_data XTOP in
  new pepr_bound_t index XTOP

let mk_number_pepr_bound_lb (n:numerical_t) =
  let b = XPSET (mk_number_pex_pset_lb n) in
  let index = pd#index_pepr_bound_data b in
  new pepr_bound_t index b

let mk_number_pepr_bound_ub (n:numerical_t) =
  let b = XPSET (mk_number_pex_pset_ub n) in
  let index = pd#index_pepr_bound_data b in
  new pepr_bound_t index b

let mk_parameter_pepr_bound_lb (index:int) (size:int) =
  let b = XPSET (mk_parameter_pex_pset_lb index size) in
  let index = pd#index_pepr_bound_data b in
  new pepr_bound_t index b

let mk_parameter_pepr_bound_ub (index:int) (size:int) =
  let b = XPSET (mk_parameter_pex_pset_ub index size) in
  let index = pd#index_pepr_bound_data b in
  new pepr_bound_t index b

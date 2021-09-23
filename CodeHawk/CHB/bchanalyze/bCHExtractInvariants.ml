(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
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
   ============================================================================= *)

(* chlib *)
open CHAtlas
open CHBounds
open CHDomain
open CHIntervals
open CHNumerical
open CHNumericalConstraints
open CHPretty
open CHLanguage
open CHSymbolicSets
open CHValueSets
open CHUtils

(* chutil *)
open CHLogger

(* xpr *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHSystemSettings
open BCHVariable

(* bchlibx86 *)
open BCHAssemblyFunctions

(* bchanalyze *)
open BCHNumericalConstraints

module H = Hashtbl


module ConstraintCollections = CHCollections.Make
  (struct 
    type t = numerical_constraint_t
    let compare = numerical_constraint_compare 
    let toPretty n = n#toPretty
   end)

let pr_expr = xpr_formatter#pr_expr
let x2p = pr_expr
let expr_compare = syntactic_comparison


let tracked_locations = []


let track_location loc p =
  if List.mem loc tracked_locations then
    chlog#add ("tracked (invariant):" ^ loc) p


exception TimeOut of float * int * int

let timeout_value = ref 120.0
let set_timeout_value t = timeout_value := (float t)

let extract_ranges 
    (finfo:function_info_int) 
    (invariants:(string, (string,atlas_t) H.t) H.t) =
  H.iter (fun k v ->
    let flocinv = finfo#finv#get_location_invariant k in
    if H.mem v "intervals" then
      let inv = H.find v "intervals" in
      let domain = inv#getDomain "intervals" in
      if domain#isBottom then 
	finfo#finv#set_unreachable k "intervals"
      else
	let vars = domain#observer#getObservedVariables in
	let vars = List.filter (fun v -> not v#isTmp) vars in 
	let vars = List.filter (fun v -> not (flocinv#is_constant v)) vars in
	let varObserver = domain#observer#getNonRelationalVariableObserver in
	List.iter (fun v ->
	  let varIntv = (varObserver v)#toInterval in
	  if varIntv#isTop then () else 
	    finfo#finv#add_interval_fact k v varIntv) vars)
         invariants

    
let extract_external_value_equalities  
    (finfo:function_info_int)
    (iaddr:string) 
    (domain:domain_int) 
    (flocinv:location_invariant_int) 
    starttime =
  let rec expand_symbolic_values x =
    let _ =
      track_location
        iaddr
        (LBLOCK [
             STR "expand-symbolic-value: "; x2p x]) in
    match  x with
    | XVar v when finfo#env#is_symbolic_value v ->
       expand_symbolic_values (finfo#env#get_symbolic_value_expr v)
    | XOp (op,l) -> XOp (op, List.map expand_symbolic_values l)
    | _ -> x in
  let is_external_var = finfo#env#is_function_initial_value in
  let numConstraints =
    domain#observer#getNumericalConstraints ~variables:None () in
  let constraintSets = get_constraint_sets numConstraints in
  let constraintVars = new VariableCollections.set_t in
  let _ =
    List.iter
      (fun c ->
        List.iter
          (fun f -> constraintVars#add f#getVariable) c#getFactors)
      numConstraints in
  let vars = constraintVars#toList in
  (* let initialVars = List.filter is_external_var vars in *)
  let localVars = List.filter (fun v -> not (is_external_var v)) vars in

  let newConstraints = new ConstraintCollections.set_t in
  let _ =
    List.iter (fun cs ->
      let rec aux vdone todo =
	match todo with
	| [] -> ()
	| v :: tl ->
	  begin
	    (match project_out cs (List.rev_append vdone tl) with
	    | Some c -> newConstraints#addList c#get_constraints
	    | _ -> ()) ;
	    aux (v::vdone) tl
	  end in
      aux [] localVars) constraintSets in

  let make_scalar_exp factors constant =
    match factors with
    | [(c,v)] when c#equal numerical_one && constant#equal numerical_zero ->
       XVar v
    | [(c,v)] when c#equal numerical_one ->
      if constant#gt numerical_zero then 
	XOp (XPlus, [XVar v; num_constant_expr constant])
      else
	XOp (XMinus, [XVar v; num_constant_expr constant#neg])
    | l ->
      List.fold_left (fun x (c,v) ->
	  let t =
            if c#abs#equal numerical_one then
	      XVar v
	    else
              XOp (XMult, [num_constant_expr c#abs; XVar v]) in
	let op = if c#gt numerical_zero then XPlus else XMinus in
	XOp (op, [x ; t])) (num_constant_expr constant) l in
  
  let get_frozen_exp
        (k: numerical_constraint_t)
        (invert_factors: bool)
        (factors: numerical_factor_t list)
        (constant: numerical_t): xpr_t option =
    try
      let factors = if invert_factors then
	  List.map (fun f -> ((k#getCoefficient f)#neg, f#getVariable)) factors
	else
	  List.map (fun f -> (k#getCoefficient f, f#getVariable)) factors in
      let constant = if invert_factors then constant else constant#neg in
      Some (make_scalar_exp factors constant )
    with
    | BCH_failure p ->
      begin
	ch_error_log#add "get-frozen-exp"
	  (LBLOCK [
               finfo#get_address#toPretty;
               STR ": ";
               k#toPretty;
               STR " - ";
               p]) ;
	None
      end in
  
  List.fold_left (fun acc (c:numerical_constraint_t) ->
      let _ =
        track_location
          iaddr
          (LBLOCK [c#toPretty]) in
    match c#getFactors with
    | [ f ] ->
      let v = f#getVariable in
      if (c#getCoefficient f)#equal numerical_one
         || (c#getCoefficient f)#equal numerical_one#neg then
	if (c#getCoefficient f)#equal numerical_one then
	  begin
            finfo#finv#add_constant_fact iaddr v c#getConstant;    (* p = c *)
            v :: acc
          end
	else 
          begin
            finfo#finv#add_constant_fact iaddr v c#getConstant#neg;  (* -p = c *)
            v :: acc
          end
      else
	acc
    | l ->
      let (pfactors,ffactors) =                      (* p = sum (c_i . f_i) *)
	List.fold_left (fun (pf,ff) f ->
	    if is_external_var f#getVariable then
              (pf,f::ff)
            else
              (f::pf,ff)) ([],[]) l in
      match (pfactors,ffactors) with
      | ([], _) -> acc
      | ([pf], ff :: _) when
	  let pc = c#getCoefficient pf in
	  pc#equal numerical_one || pc#neg#equal numerical_one ->
	 begin
	   (* invert the factors if the coefficient of the program variable equals
	      one otherwise invert the constant *)
	   match get_frozen_exp
                   c
                   ((c#getCoefficient pf)#equal numerical_one)
	           ffactors c#getConstant with
	   | Some fexp ->
	      let v = pf#getVariable in
              let fexpx = simplify_xpr (expand_symbolic_values fexp) in
	      begin
                finfo#finv#add_symbolic_expr_fact iaddr v fexpx ;
                v :: acc
              end
	   | _ -> acc
	 end
      | _ -> acc) [] newConstraints#toList


let extract_relational_facts finfo iaddr domain =
  let constraints = domain#observer#getNumericalConstraints ~variables:None () in
  List.iter (finfo#finv#add_lineq iaddr) constraints

let extract_testvar_equalities finfo iaddr domain =
  let env = finfo#env in
  let vars = domain#observer#getObservedVariables in
  let fvals = List.filter env#is_frozen_test_value vars in
  List.fold_left (fun acc fval ->
    let (fvar,taddr,jaddr) = env#get_frozen_variable fval in
    if iaddr = jaddr then
      let varsout = List.filter (fun v -> not ((fvar#equal v) || (fval#equal v))) vars in
      let domain = domain#projectOut varsout in
      let numConstrs = domain#observer#getNumericalConstraints ~variables:None () in
      match numConstrs with 
      | [] -> acc 
      | _ -> 
	 begin
	   finfo#finv#add_test_value_fact iaddr fvar fval taddr jaddr ;
	   fval :: acc
	end
    else acc) [] fvals

let extract_initvar_equalities finfo iaddr domain flocinv =
  let get_var_constraints constraint_sets v1 v2 domvars =
    let numCs = new ConstraintCollections.set_t in
    let _ = List.iter (fun cs ->
      if cs#has v1 && cs#has v2 then
	let outvars = List.filter (fun v -> not ((v1#equal v) || (v2#equal v))) domvars in 
	match project_out cs outvars with
	| Some c -> numCs#addList c#get_constraints
	| _ -> ()) constraint_sets in
    numCs#toList in
  let is_equality c v1 v2 = 
    c#getConstant#equal numerical_zero &&
      (let factors = c#getFactors in
       match factors with 
       | [ f1 ; f2 ] ->
	 let c1 = c#getCoefficient f1 in
	 let c2 = c#getCoefficient f2 in
	 c1#neg#equal c2 && (c1#equal numerical_one || c2#equal numerical_one)
       | _ -> false) in
  let have_equal_values c1 c2 =
    match (c1#getFactors,c2#getFactors) with
    | ([ f1 ],[ f2 ]) -> c1#getConstant#equal c2#getConstant
    | _ -> false in
  let env = finfo#env in
  let domVars = domain#observer#getObservedVariables in
  let fvals = List.filter env#is_initial_value domVars in
  let fvalsEq = flocinv#get_init_equalities in
  let fvalsNotEq = flocinv#get_init_disequalities in
  let numConstraints = domain#observer#getNumericalConstraints ~variables:None () in
  let constraintSets = get_constraint_sets numConstraints in 
  let disequalities = ref [] in
  let add_disequality fvar fval =
    begin
      finfo#finv#add_initial_disequality_fact iaddr fvar fval ;
      if finfo#env#is_initial_memory_value fval then
	disequalities  := (fvar,fval) :: !disequalities
    end in  
  let propagate_disequalities l = () in
  let fvars =
    List.fold_left
      (fun acc fval ->
        let fvar = env#get_init_value_variable fval in
        if List.exists (fun v -> v#equal fval) fvalsEq then 
          fvar :: acc
        else if List.exists (fun v -> v#equal fval) fvalsNotEq then
          acc 
        else if List.exists (fun v -> v#equal fvar) domVars then
          let numcs = get_var_constraints constraintSets fvar fval domVars in 
          match numcs with 
          | [] -> begin add_disequality fvar fval ; acc end
          | [ c ] when is_equality c fvar fval ->
	     begin finfo#finv#add_initial_value_fact iaddr fvar fval ; fvar :: acc end
          | [ c1 ; c2 ] when have_equal_values c1 c2 ->
	     begin finfo#finv#add_initial_value_fact iaddr fvar fval ; fvar :: acc end
          | _ -> begin add_disequality fvar fval ; acc end
        else 
          begin add_disequality fvar fval ; acc end) [] fvals in
  let _ = match !disequalities with [] -> () | l -> propagate_disequalities l in
  fvars

let extract_linear_equalities 
    (finfo:function_info_int)
    (invariants:(string, (string,atlas_t) H.t) H.t) =
  let starttime = Unix.gettimeofday () in
  let outside_test_jump_range v k = 
    finfo#env#is_frozen_test_value v &&
      not (finfo#env#is_in_test_jump_range v k) in
  let invList = ref [] in
  let _ = H.iter (fun k v -> invList := (k,v) :: !invList) invariants in
  let invList = List.sort (fun (k1,_) (k2,_) -> Stdlib.compare k1 k2) !invList in
  try
    List.iter (fun (k, v) ->
      if H.mem v "karr" then
	let inv = H.find v "karr" in
	let flocinv = finfo#finv#get_location_invariant k in
	let knownVars = flocinv#get_known_variables in
	let domain = inv#getDomain "karr" in
	let vars = domain#observer#getObservedVariables in
	let outvars =
          List.filter (fun v -> v#isTmp || outside_test_jump_range v k) vars in
        let _ =
          track_location
            k
            (LBLOCK [
                 STR "lineareq: "; NL;
                 STR "knownVars: ";
                 pretty_print_list knownVars (fun v -> v#toPretty) "[" "," "]";
                 NL;
                 STR "outvars: ";
                 pretty_print_list outvars (fun v -> v#toPretty) "[" "," "]"]) in
	let domain = domain#projectOut outvars in
	let initVars = extract_initvar_equalities finfo k domain flocinv in
	let testVals = extract_testvar_equalities finfo k domain in
        let _ =
          track_location
            k
            (LBLOCK [
                 STR "testVals: ";
                 pretty_print_list testVals (fun v -> v#toPretty) "[" "," "]";
                 NL;
                 STR "initVars: ";
                 pretty_print_list initVars (fun v -> v#toPretty) "[" "," "]"]) in
	let domain = domain#projectOut (knownVars @ initVars @ testVals) in
	let extVars =
          extract_external_value_equalities finfo k domain flocinv starttime in
	let domain = domain#projectOut extVars in
	extract_relational_facts finfo k domain) invList
  with
    TimeOut (timeUsed,nVars,nExternalVars) ->
      pr_debug [ STR "Timeout: " ; STR (Printf.sprintf "%4.1f" timeUsed) ; STR " secs" ;
		 STR " (" ; INT nVars ; STR "vars; " ; INT nExternalVars ; 
		 STR " external vars)" ; NL ] 

let extract_valuesets
    (finfo:function_info_int) 
    (invariants:(string, (string,atlas_t) H.t) H.t) =
  H.iter (fun k v ->
    if H.mem v "valuesets" then
      let inv = H.find v "valuesets" in
      let flocinv = finfo#finv#get_location_invariant k in
      let domain = inv#getDomain "valuesets" in
      let varObserver = domain#observer#getNonRelationalVariableObserver in
      let vars = domain#observer#getObservedVariables in
      let knownvars = flocinv#get_known_variables in
      let vars = List.filter (fun v -> not (v#isTmp || List.mem v knownvars)) vars in
      List.iter (fun (v:variable_t) ->
	let valueset = (varObserver v)#toValueSet in
	if valueset#isTop then () else
	  if valueset#removeZeroOffset#isSingleBase then
	    let (base,offset) = valueset#removeZeroOffset#getSingleBase in
	    let canbenull:bool = valueset#includesZero in
	    if v#getName#equal base then () else
	    finfo#finv#add_valueset_fact k v base offset canbenull) vars) invariants


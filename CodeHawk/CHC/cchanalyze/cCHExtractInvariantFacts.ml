(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHNumericalConstraints
open CHPEPRTypes
open CHPEPRBounds
open CHPretty
open CHSymbolicSets

(* chutil *)
open CHLogger
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprTypes
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHUtilities

(* cchpre *)
open CCHPreTypes
open CCHInvariantFact

(* cchanalyze *)
open CCHAnalysisTypes
open CCHNumericalConstraints

module H = Hashtbl


exception TimeOut of float


let get_context name =
  if (String.length name) > 4 && (String.sub name 0 4) = "inv_" then
    let fs = nsplit '_' name in
    match fs with
    | [_; ctxt; _] ->
       (try
          ccontexts#get_context (int_of_string ctxt)
        with
        | Failure _ ->
           raise
             (CCHFailure
                (LBLOCK [STR "get_context: int_of_string on "; STR ctxt])))
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "unexpected format for invariant name: ";
                 STR name]))
  else
    raise
      (CCHFailure
         (LBLOCK [STR "unexpected invariant name: "; STR name]))


let timeout_value = ref 120.0
let set_timeout_value t = timeout_value := (float t)


let extract_external_value_pairs
      (env:c_environment_int)
      _start_time
      (inv:atlas_t):(variable_t * non_relational_value_t) list =
  let fname = env#get_functionname in
  let get_index v = v#getName#getSeqNumber in
  let is_program_var v = env#is_program_variable v in
  let is_fixed_value v = env#is_fixed_value v in
  let is_indexed v = not (v#isTmp) && (get_index v) >= 0 in
  let domain = inv#getDomain linear_equalities_domain in
  let vars = domain#observer#getObservedVariables in
  let programVars = List.filter is_program_var vars in
  let unIndexedVars = List.filter (fun v -> not (is_indexed v)) vars in
  let domain = domain#projectOut unIndexedVars in
  let numConstraints =
    domain#observer#getNumericalConstraints ~variables:None () in
  let constraintSets = get_constraint_sets numConstraints in
  let newConstraints = mk_constraint_set () in
  let _ =
    List.iter (fun cs ->
      let rec aux d todo =
	match todo with
	| [] -> ()
	| v :: tl ->
	  begin
	    (match project_out cs (List.rev_append d tl) with
             | Some c -> List.iter newConstraints#add c#get_constraints
	     | _ -> ());
	    aux (v::d) tl
	  end in
      aux [] programVars) constraintSets in

  let make_scalar_exp factors constant =
    match factors with
    | [(c,v)] when c#equal numerical_one && constant#equal numerical_zero ->
	Some (XVar v)
    | [(c,v)] when c#equal numerical_one ->
       if constant#gt numerical_zero then
         Some (XOp (XPlus, [XVar v; num_constant_expr constant]))
       else
         Some (XOp (XMinus, [XVar v; num_constant_expr constant#neg]))
    | _ -> None in

  let make_pointer_exp p scalars constant =
    try
      match scalars with
      | [] when constant#equal numerical_zero -> Some (XVar p)
      | [] ->
         if constant#gt numerical_zero then
           Some (XOp (XPlus, [XVar p; num_constant_expr constant]))
         else
           Some (XOp (XMinus, [XVar p; num_constant_expr constant#neg]))
      | _ -> None
    with
    | CCHFailure p ->
      begin
	ch_error_log#add "make-pointer-exp"
	  (LBLOCK [STR "Extract invariants "; p]);
	None
      end in

  let make_pointer_subtraction _p1 _p2 _scalars _constant =
    None in

  let get_symbolic_expr
        (konstraint:numerical_constraint_t)
        invert_factors
        (factors:numerical_factor_t list)
        (constant:numerical_t):xpr_t option =
    try
      let factors =
        if invert_factors then
	  List.map (fun f ->
              ((konstraint#getCoefficient f)#neg, f#getVariable)) factors
	else
	  List.map (fun f ->
              (konstraint#getCoefficient f, f#getVariable)) factors in
      let constant = if invert_factors then constant else constant#neg in
      let pointerVariables =
        List.filter (fun (_, v) ->
            let t = env#get_variable_type v in
	    match t with TPtr _ -> true | _ -> false) factors in
      match pointerVariables with
      | [] -> make_scalar_exp factors constant

	(* x = ptr + scalars + constant *)
      | [(c, p)] when c#equal numerical_one ->
	 let scalars = List.filter (fun (_,v) -> not (v#equal p)) factors in
	 make_pointer_exp p scalars constant

	(* x = ptr1 - ptr2 + scalars + constant *)
      | [(c1, p1); (c2, p2)] when c1#equal c2#neg && c1#equal numerical_one ->
	 let scalars =
           List.filter (fun (_,v) ->
               not ((v#equal p1) || (v#equal p2))) factors in
	 make_pointer_subtraction p1 p2 scalars constant

        (* x = ptr2 - ptr1 + scalars + constant *)
      | [(c1, p1); (c2, p2)] when c1#equal c2#neg && c2#equal numerical_one ->
	 let scalars =
           List.filter (fun (_,v) ->
               not ((v#equal p1) || (v#equal p2))) factors in
	 make_pointer_subtraction p2 p1 scalars constant

        (* two pointers in different configuration *)
      | [(_, p1); (_, p2)] ->
	begin
	  ch_info_log#add
            "constraint with two pointers"
	    (LBLOCK [
                 STR fname;
                 STR ": ";
                 konstraint#toPretty;
		 STR " with pointer variables ";
                 p1#toPretty;
                 STR " and ";
		 p2#toPretty]);
	  None
	end
       (* more than two pointers in expression *)
      | _ ->
	begin
	  ch_info_log#add
            "constraint with multiple pointers"
	    (LBLOCK [
                 STR fname;
                 STR ": ";
                 konstraint#toPretty;
		 STR " with pointer variables";
		 pretty_print_list
                   pointerVariables
		   (fun (_,v) -> v#toPretty) "[" ";" "]"]);
	  None
	end
    with
    | CCHFailure p ->
      begin
	ch_error_log#add
          "get-frozen-exp"
	  (LBLOCK [
               STR "Extract invariants "; konstraint#toPretty; STR ": "; p]);
	None
      end in

  List.fold_left (fun acc (c:numerical_constraint_t) ->
      match c#getFactors with
      | [f] when is_program_var f#getVariable ->
         let pval = f#getVariable in
         if (c#getCoefficient f)#equal numerical_one
            || (c#getCoefficient f)#equal numerical_one#neg then
	   if (c#getCoefficient f)#equal numerical_one then  (* p = c *)
	     let num = c#getConstant in
	     (pval, FIntervalValue (Some num, Some num)) :: acc
	   else if (c#getCoefficient f)#equal numerical_one#neg then   (* -p = c *)
	     let num = c#getConstant#neg in
	     (pval, FIntervalValue (Some num, Some num)) :: acc
	   else
	     begin
	       ch_info_log#add
                 "unexpected constraint"
	         (LBLOCK [STR fname; STR ": "; c#toPretty]);
	       acc
	     end
	 else
	   acc
      | l ->                                          (* p = sum (c_i . f_i) *)
         let (pfactors, ffactors) =
           List.fold_left (fun (pf, ff) f ->
	       if is_program_var f#getVariable then
	         (f::pf, ff)
	       else if is_fixed_value f#getVariable then
	         (pf, f::ff)
	       else
	         begin
	           ch_error_log#add
                     "unexpected variable in constraint"
	             (LBLOCK [
                          STR fname;
                          STR ": ";
                          f#getVariable#toPretty;
                          STR " in ";
			  c#toPretty]);
	           (pf,ff)
	         end) ([], []) l in
         match (pfactors,ffactors) with
         | ([], _) -> acc
         | ([pf], _ff::_)
              when let pcoeff = c#getCoefficient pf in
		   pcoeff#equal numerical_one || pcoeff#neg#equal numerical_one ->
	    begin
	      (* invert the factors if the coefficient of the program
                 variable equals one
	         otherwise invert the constant *)
	      match get_symbolic_expr
                      c
                      ((c#getCoefficient pf)#equal numerical_one)
	              ffactors c#getConstant with
	      | Some fxpr -> (pf#getVariable, FSymbolicExpr fxpr) :: acc
	      | _ -> acc
	    end
         | _ -> acc) [] newConstraints#get_constraints


let extract_external_value_facts
      (env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  let startTime = Unix.gettimeofday ()  in
  let numInvariants = H.length invariants in
  let currentContext = ref 0 in
  try
    H.iter (fun k v ->
	if H.mem v linear_equalities_domain then
	  let _ = currentContext := !currentContext + 1 in
	  let timeUsed = (Unix.gettimeofday ()) -. startTime in
	  let _ = if timeUsed > !timeout_value then
		    raise (TimeOut timeUsed) in
	  let inv = H.find v linear_equalities_domain in
	  let context = get_context k in
	  let pairs = extract_external_value_pairs env startTime inv in
          let facts = List.map (fun (v,f) -> NonRelationalFact (v, f)) pairs in
          List.iter (fun f -> invio#add_fact context f) facts) invariants
  with
    TimeOut timeUsed ->
    ch_info_log#add
      "time-out"
      (LBLOCK [
           STR env#get_functionname;
           STR ": ";
	   STR (Printf.sprintf "%4.1f" timeUsed);
           STR " secs";
	   STR "(invariants: ";
           INT numInvariants;
	   STR "; current location: ";
           INT !currentContext;
           STR ")";
           NL])


let extract_ranges
      (env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  let get_bound b =
    match b with MINUS_INF | PLUS_INF -> None | NUMBER n -> Some n in
  let is_cvv v = env#is_fixed_value v in
  H.iter (fun k v ->
    if H.mem v intervals_domain then
      let inv = H.find v intervals_domain in
      let context = get_context k in
      let domain = inv#getDomain intervals_domain in
      if domain#isBottom then
        invio#add_fact context (Unreachable "intervals")
      else
	let vars = domain#observer#getObservedVariables in
	let programVars = List.filter (fun v -> not (is_cvv v || v#isTmp)) vars in
	let varObserver = domain#observer#getNonRelationalVariableObserver in
	List.iter(fun v ->
	    let index = v#getName#getSeqNumber in
	    if index >= 0 then
	      let varIntv = (varObserver v)#toInterval in
              if varIntv#isTop then () else
	        let lb = get_bound varIntv#getMin#getBound in
                let ub = get_bound varIntv#getMax#getBound in
	        let invValue = FIntervalValue (lb, ub) in
                let fact = NonRelationalFact (v, invValue) in
                invio#add_fact context fact) programVars) invariants


let extract_pepr
      (env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  let params = mk_pepr_params env#get_parameters in
  let get_bound b =
    match b with MINUS_INF | PLUS_INF -> None | NUMBER n -> Some n in
  H.iter (fun k v ->
      if H.mem v pepr_domain then
        let inv = H.find v pepr_domain in
        let context = get_context k in
        let domain = inv#getDomain pepr_domain in
        if domain#isBottom then
          invio#add_fact context (Unreachable "pepr")
        else
          let vars = domain#observer#getObservedVariables in
          let varObserver = domain#observer#getNonRelationalVariableObserver in
          List.iter (fun v ->
              let index = v#getName#getSeqNumber in
              if index > 0 || v#getName#getBaseName = "$env$" then
                let vPepr = (varObserver v)#toPEPRValue in
                match vPepr#get_value with
                | PEPRTOP -> ()
                | PEPRDEP d ->
                   let depxprs = get_pepr_dependency_xprs params d in
                   List.iter (fun x ->
                       invio#add_fact context (ParameterConstraint x)) depxprs
                | PEPRANGE r ->
                  let peprX = get_pepr_range_xprs params r in
                  begin
                    (match peprX.pepr_n with
                     | Some n ->
                        let invValue = FIntervalValue (Some n, Some n) in
                        let fact = NonRelationalFact (v, invValue) in
                        invio#add_fact context fact
                     | _ -> ());
                    (match peprX.pepr_i with
                     | Some i ->
                        let lb = get_bound i#getMin#getBound in
                        let ub = get_bound i#getMax#getBound in
                        let invValue = FIntervalValue (lb, ub) in
                        let fact = NonRelationalFact (v, invValue) in
                        invio#add_fact context fact
                     | _ -> ());
                    (List.iter (fun x ->
                         let invValue = FSymbolicExpr x in
                         let fact = NonRelationalFact (v, invValue) in
                         invio#add_fact context fact) peprX.pepr_equalities);
                    (List.iter (fun (bt,xll) ->
                         let invValue = FSymbolicBound (bt, xll) in
                         let fact = NonRelationalFact (v, invValue) in
                         invio#add_fact context fact) peprX.pepr_bounds)
                  end) vars) invariants


let extract_base_values
      (env:c_environment_int) (inv:atlas_t):invariant_fact_t list =
  let result = ref [] in
  let domain = inv#getDomain valueset_domain in
  let varObserver = domain#observer#getNonRelationalVariableObserver in
  let vars = domain#observer#getObservedVariables in
  let programVars = List.filter env#is_program_variable vars in
  let  _ = List.iter (fun v ->
    let valueset = (varObserver v)#toValueSet in
    if valueset#isTop then ()
    else
      if valueset#removeZeroOffset#isSingleBase then
	let (base,offset) = valueset#removeZeroOffset#getSingleBase in
	let (lb, ub) = if offset#isTop then (None,None) else
	    let lb = match offset#getMin#getBound with
		MINUS_INF | PLUS_INF -> None | NUMBER n -> Some n in
	    let ub = match offset#getMax#getBound with
		MINUS_INF | PLUS_INF -> None | NUMBER n -> Some n in
	    (lb, ub) in
	let (a, bVar) =
          if env#get_variable_manager#is_fixed_value base#getSeqNumber then
	    (External, XVar (new variable_t base NUM_VAR_TYPE))
	  else
            (Heap, XConst (IntConst numerical_zero)) in
	let canbeNull = valueset#includesZero in
	let invValue = FBaseOffsetValue (a, bVar, lb, ub, canbeNull) in
        let fact = NonRelationalFact (v, invValue) in
        result := fact :: !result
      else
	()) programVars  in
  !result


let extract_symbol_facts domainname (inv:atlas_t):invariant_fact_t list =
  let result = ref [] in
  let domain = inv#getDomain domainname in
  if domain#isBottom then
    [Unreachable domainname]
  else
    let varObserver = domain#observer#getNonRelationalVariableObserver in
    let vars = domain#observer#getObservedVariables in
    let programVars = List.filter (fun v -> not v#isTmp) vars in
    let _ =
      List.iter (fun v ->
          let varIntv = (varObserver v)#toSymbolicSet in
          if varIntv#isTop then () else
            match varIntv#getSymbols with
            | SET symbols ->
               let symbols =
                 (List.sort (fun s1 s2 ->
                      Stdlib.compare
                        s1#getBaseName s2#getBaseName) symbols#toList) in
               let invValue =
                 if domainname = symbolic_sets_domain then
                   FInitializedSet symbols
                 else
                   FRegionSet symbols in
               let fact = NonRelationalFact (v, invValue) in
               result := fact :: !result
            | _ -> ()) programVars in
    !result


let extract_state_facts domainname (inv:atlas_t):invariant_fact_t list =
  let result = ref [] in
  let domain = inv#getDomain domainname in
  if domain#isBottom then
    [Unreachable domainname]
  else
    let varObserver = domain#observer#getNonRelationalVariableObserver in
    let vars = domain#observer#getObservedVariables in
    let programVars = List.filter (fun v -> not v#isTmp) vars in
    let _ =
      List.iter (fun v ->
          let varIntv = (varObserver v)#toSymbolicSet in
          if varIntv#isTop then () else
            match varIntv#getSymbols with
            | SET symbols ->
               let symbols =
                 (List.sort (fun s1 s2 ->
                      Stdlib.compare
                        s1#getBaseName s2#getBaseName) symbols#toList) in
               let invValue =
                 if domainname = "state sets" then
                   FPolicyStateSet symbols
                 else
                   FRegionSet symbols in
               let fact = NonRelationalFact (v, invValue) in
               result := fact :: !result
            | _ -> ()) programVars in
    !result


let extract_valuesets
      (env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  try
    H.iter (fun k v ->
        if H.mem v valueset_domain then
	  let inv = H.find v valueset_domain in
	  let context = get_context k in
	  let facts = extract_base_values env inv in
          List.iter (fun f -> invio#add_fact context f) facts) invariants
  with
  | CCHFailure p ->
     raise
       (CCHFailure
          (LBLOCK [STR "Error in extracting valueset invariants: "; p]))


let extract_symbols
      (_env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  try
    H.iter (fun k v ->
        if H.mem v symbolic_sets_domain then
          let inv = H.find v symbolic_sets_domain in
          let context = get_context k in
          let facts = extract_symbol_facts symbolic_sets_domain inv in
          List.iter (fun f -> invio#add_fact context f) facts) invariants
  with
  | CCHFailure p ->
     raise
       (CCHFailure
          (LBLOCK [STR "Error in extracting symbolic invariants: "; p]))


let extract_states
      (_env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  try
    H.iter (fun k v ->
        if H.mem v "state sets" then
          let inv = H.find v "state sets" in
          let context = get_context k in
          let facts = extract_state_facts "state sets" inv in
          List.iter (fun f -> invio#add_fact context f) facts) invariants
  with
  | CCHFailure p ->
     raise
       (CCHFailure
          (LBLOCK [STR "Error in extracting state invariants: "; p]))


let extract_sym_pointersets
      (_env:c_environment_int)
      (invio:invariant_io_int)
      (invariants:(string, (string,atlas_t) H.t) H.t) =
  try
    H.iter (fun k v ->
        if H.mem v sym_pointersets_domain then
          let inv = H.find v sym_pointersets_domain in
          let context = get_context k in
          let facts = extract_symbol_facts sym_pointersets_domain inv in
          List.iter (fun f -> invio#add_fact context f) facts) invariants
  with
  | CCHFailure p ->
     raise (CCHFailure (LBLOCK [STR "Error in extracting pointersets: "; p]))

(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
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
   ============================================================================= *)

(* chlib *)
open CHLanguage
open CHLinearEqualitiesDomainNoArrays
open CHNumerical
open CHNumericalConstraints
open CHPretty
open CHUtils

(* chutil *)
open CHLogger

(* cchlib *)
open CCHUtilities

(* cchanalyze *)
open CCHAnalysisTypes

exception CCHConstraintFailure of int * int * numerical_constraint_t list

let list_compare f l1 l2  =
  List.fold_left2 (fun acc x1 x2 -> if acc = 0 then f x1 x2 else acc) 0 l1 l2

(* Comparison:
    1: compare constants
    2: compare number of factors
    3: compare factors
    4: compare coefficients
*)
let numerical_constraint_compare c1 c2 = 
  let fcompare f1 f2 = f1#compare f2 in
  let l1 = c1#getConstant#compare c2#getConstant in
  if l1 = 0 then
    let fl1 = c1#getFactors in
    let fl2 = c2#getFactors in
    let l2 = Pervasives.compare (List.length fl1) (List.length fl2) in
    if l2 = 0 then
      let fl1 = List.sort fcompare fl1 in
      let fl2 = List.sort fcompare fl2 in
      let l3 = list_compare fcompare fl1 fl2 in
      if l3 = 0 then
	List.fold_left (fun acc f ->
	  if acc = 0 then
	    (c1#getCoefficient f)#compare (c2#getCoefficient f)
	  else
	    acc) 0 fl1
      else l3
    else l2
  else l1
	
module ConstraintCollections = CHCollections.Make
  (struct 
    type t = numerical_constraint_t
    let compare = numerical_constraint_compare 
    let toPretty n = n#toPretty
   end)

class constraint_set_t:constraint_set_int =
object (self)
  val constraints = new ConstraintCollections.set_t
  val variables = new VariableCollections.set_t 

  method add c = 
    begin
      constraints#add c ;
      List.iter (fun f -> variables#add f#getVariable) c#getFactors
    end

  method get_constraints = constraints#toList

  method has = variables#has

  method project_out (vars:variable_t list) =
    if List.exists self#has vars then
      if constraints#size = 1 then
        None
      else
	let vset = new VariableCollections.set_t in
	let cset = new ConstraintCollections.set_t in
	let dom = (new linear_equalities_domain_no_arrays_t)#mkEmpty in
	let dom = dom#importNumericalConstraints constraints#toList in
	let dom = dom#projectOut vars in
	let cs = dom#observer#getNumericalConstraints ~variables:None () in
	let _ =
          List.iter (fun c -> 
	      begin (List.iter (fun f ->
                         vset#add f#getVariable) c#getFactors) ; cset#add c end) cs in
	Some {< variables = vset ; constraints = cset >} 
    else
      Some {< >}

  method private project_out_one (v:variable_t) = 
    if variables#has v then
      let newSet = new ConstraintCollections.set_t in
      let eliminate (c1:numerical_constraint_t) cs =
	List.iter (fun (c2:numerical_constraint_t) -> 
	  if c2#getVariables#has v then
	    let factor = new numerical_factor_t v in
	    let coeff1 = c1#getCoefficient factor in
	    let coeff2 = c2#getCoefficient factor in
	    let _ =
              if coeff1#equal numerical_zero || coeff2#equal numerical_zero then
		raise (CCHFailure
                         (LBLOCK [ STR "Internal error in elimination of " ;
                                   v#toPretty ; STR " in " ; c1#toPretty ;
                                   STR " and " ; c2#toPretty ])) in
	    let newC = c1#affineCombination coeff2#neg coeff1 c2 in
	    if newC#isTrivial then
	      ()
	    else
	      let _ = newC#normalize in
	      newSet#add newC) cs in
      let rec aux l =
	match l with
	| [] -> ()
	| c::tl ->
	  let _ = if c#getVariables#has v then 
	      eliminate c tl 
	    else
	      newSet#add c in
	  aux tl in
      let _ = aux constraints#toList in
      let newVariables = variables#filter (fun vv -> not (v#equal vv)) in
      if newSet#size > constraints#size + 10 then
	raise (CCHConstraintFailure (constraints#size, newSet#size, constraints#toList))
      else
	{< constraints = newSet ; variables = newVariables >}
    else
      {< >}

  method toPretty = 
    LBLOCK [ STR "variables: (" ; INT variables#size ; STR ")" ; NL ; 
	     INDENT (3, LBLOCK [ pretty_print_list variables#toList
				   (fun v -> LBLOCK [ v#toPretty ; NL ]) "" "" "" ]) ; NL ;
	     STR "constraints: (" ; INT constraints#size ; STR ")" ; NL ; 
	     INDENT (3, LBLOCK [ pretty_print_list constraints#toList
				   (fun c -> LBLOCK [ c#toPretty ; NL ]) "" "" "" ]) ; NL ]
end

let project_out (c:constraint_set_t) (vars:variable_t list) =  c#project_out vars

let set_union l =
  let constraints = List.concat (List.map (fun s -> s#get_constraints) l) in
  let s = new constraint_set_t in
  let _ = List.iter s#add constraints in
  s

let mk_constraint_set () = new constraint_set_t

let get_constraint_sets constraints =
  List.fold_left (fun acc c ->
    let cvars = List.map (fun f -> f#getVariable) c#getFactors in
    let (hasv,nothasv) = List.fold_left (fun (h,n) cs -> 
      if List.exists (fun v -> cs#has v) cvars then
	(cs::h,n)
      else
	(h,cs::n)) ([],[]) acc in
    match hasv with
    | [] -> 
      let newset = new constraint_set_t in
      begin newset#add c ; newset :: acc end
    | [ s ] -> begin s#add c ; acc end
    | _ ->
      let newset = set_union hasv in
      begin newset#add c ; newset :: nothasv end) [] constraints

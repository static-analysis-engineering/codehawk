(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(** Pretty printer for various forms of numerical constraints *)

(* chlib *)
open CHLanguage
open CHNumerical
open CHNumericalConstraints
open CHPretty


let rec find_first preference_lst lst =
  match preference_lst with
  | [] -> None
  | h::tl -> if List.mem h lst then Some h else find_first tl lst


let kind_to_pretty ?(reverse = false) c =
  match c#getKind with
  | LINEAR_EQ -> STR " = "
  | LINEAR_INEQ -> if reverse then STR " >= " else STR " <= "


class type num_constraint_printer_int =
object
  method print:
           ?lhs:variable_t list ->
           ?rhs:variable_t list ->
           numerical_constraint_t ->
           pretty_t
end


class num_constraint_printer_t =
object (self)

  (* pretty print numerical constraints with variables in lhs on the left,
     or variables in rhs on the right of the (in)equality sign. Only lhs or
     rhs can be specified, not both.
   *)
  method print ?(lhs=[]) ?(rhs=[]) (c:numerical_constraint_t):pretty_t =
    match (lhs,rhs) with
    | ([],[]) -> self#print_standard c
    | ([],_ ) -> self#print_with_rhs rhs c
    | (_, []) -> self#print_with_lhs lhs c
    | _ ->
       raise
         (CHCommon.CHFailure
	    (LBLOCK [
                 STR "Cannot constrain both lhs and rhs in numerical ";
                 STR "constraint printer"]))

  method private cst_to_pretty ?(sole_factor=false) c =
    if sole_factor then
      c#toPretty
    else if c#equal numerical_zero then
      STR ""
    else if c#gt numerical_zero then
      LBLOCK [STR " + "; c#toPretty]
    else
      LBLOCK [STR " - "; c#neg#toPretty]

  method private factors_to_pretty factors =
    let coeff first c =
      if c#equal numerical_one then
        if first then
          STR ""
        else
          STR " + "
      else if c#equal numerical_one#neg then
        STR " - "
      else if c#lt numerical_zero then
        c#toPretty
      else
        LBLOCK [(if first then STR "" else STR " + "); c#toPretty] in
    let (pl, _) =
      List.fold_left (fun (a,first) (c,f) ->
	  ((LBLOCK [coeff first c; f#toPretty]):: a, false)) ([],true) factors in
    LBLOCK (List.rev pl)

  method private factors_cst_to_pretty factors cst =
    match factors with
    | [] -> self#cst_to_pretty ~sole_factor:true cst
    | _ ->
       LBLOCK [self#factors_to_pretty factors; self#cst_to_pretty cst]

  method private print_standard c =
    let vars = c#getVariablesList in
    let len = List.length vars in
    if len = 0 then c#toPretty
    else
      let factors = c#getFactorsList in
      if len = 1 then
	let (lhs_coeff,lhs_factor) = List.hd factors in
	if lhs_coeff#gt numerical_zero then
	  c#toPretty
	else
	  let lhs_coeff = lhs_coeff#neg in
	  let cst = c#getConstant#neg in
	  let lhs_pretty = self#factors_to_pretty [(lhs_coeff,lhs_factor)] in
	  let rhs_pretty = self#cst_to_pretty ~sole_factor:true cst in
	  LBLOCK [lhs_pretty; kind_to_pretty ~reverse:true c; rhs_pretty]
      else if len = 2 then
	let (lhs_coeff,lhs_factor) = List.hd factors in
	if lhs_coeff#lt numerical_zero then
	  let lhs_coeff = lhs_coeff#neg in
	  let rhs_factors = List.tl factors in
	  let cst = c#getConstant#neg in
	  let lhs_pretty = self#factors_to_pretty [(lhs_coeff,lhs_factor)] in
	  let rhs_pretty = self#factors_cst_to_pretty rhs_factors cst in
	  LBLOCK [lhs_pretty; kind_to_pretty ~reverse:true c; rhs_pretty]
	else
	  let rhs_factors = List.map (fun (c,f) -> (c#neg,f)) (List.tl factors) in
	  let cst = c#getConstant in
	  let lhs_pretty = self#factors_to_pretty [(lhs_coeff,lhs_factor)] in
	  let rhs_pretty = self#factors_cst_to_pretty rhs_factors cst in
	  LBLOCK [lhs_pretty; kind_to_pretty c; rhs_pretty]
      else
	c#toPretty

  method private print_with_lhs preference c =
    let vars = c#getVariablesList in
    let lhs_var = find_first preference vars in
    match lhs_var with
    | None -> c#toPretty
    | Some v ->
       let cst = c#getConstant in
       let factors = c#getFactorsList in
       let (lhs_factors,rhs_factors) =
         List.partition (fun (_,f) -> v#equal f#getVariable) factors in
       let (lhs_coeff,lhs_factor) = List.hd lhs_factors in
       if lhs_coeff#lt numerical_zero then
	 let lhs_coeff = lhs_coeff#neg in
	 let cst = cst#neg in
	 let lhs_pretty = self#factors_to_pretty [(lhs_coeff,lhs_factor)] in
	 let rhs_pretty = self#factors_cst_to_pretty rhs_factors cst in
	 LBLOCK [lhs_pretty; kind_to_pretty ~reverse:true c; rhs_pretty]
       else
	 let rhs_factors = List.map (fun (c,f) -> (c#neg,f)) rhs_factors in
	 let lhs_pretty = self#factors_to_pretty [(lhs_coeff,lhs_factor)] in
	 let rhs_pretty = self#factors_cst_to_pretty rhs_factors cst in
	 LBLOCK [lhs_pretty; kind_to_pretty c; rhs_pretty]

  method private print_with_rhs preference c =
    let vars = c#getVariablesList in
    let rhs_var = find_first preference vars in
    match rhs_var with
      None -> c#toPretty
    | Some v ->
       let cst = c#getConstant in
       let factors = c#getFactorsList in
       let (rhs_factors,lhs_factors) =
         List.partition (fun (_,f) -> v#equal f#getVariable) factors in
       let (rhs_coeff,rhs_factor) = List.hd rhs_factors in
       if rhs_coeff#gt numerical_zero then
	 let lhs_factors = List.map (fun (c,f) -> (c#neg,f)) lhs_factors in
	 let cst = cst#neg in
	 let rhs_pretty =
           self#factors_cst_to_pretty [(rhs_coeff,rhs_factor)] cst in
	 let lhs_pretty = self#factors_to_pretty lhs_factors in
	 LBLOCK [lhs_pretty; kind_to_pretty ~reverse:true c; rhs_pretty]
       else
	 let rhs_coeff = rhs_coeff#neg in
	 let rhs_pretty =
           self#factors_cst_to_pretty [(rhs_coeff,rhs_factor)] cst in
	 let lhs_pretty = self#factors_to_pretty lhs_factors in
	 LBLOCK [lhs_pretty; kind_to_pretty c; rhs_pretty]

end


let num_constraint_printer = new num_constraint_printer_t

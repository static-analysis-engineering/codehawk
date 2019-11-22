(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet and Anca Browne
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
open CHConstants   
open CHLocalIterationSigmaCombinator
open CHNonRelationalDomainValues
open CHNumericalConstraints   
open CHPretty   
open CHStridedIntervals

exception Bottom_found

class strided_gauss_seidel_sigma_combinator_t
        ~(linear_domain: string)
        ~(interval_domain: string)
        ~(threshold: int option) =
object (self: 'a)
     
  inherit local_iteration_sigma_combinator_with_threshold_t
            ~domain_1:linear_domain
            ~domain_2:interval_domain 
            ~threshold:(match threshold with Some t -> t | _ -> -1)
        
  method private getRange v intervals =
    let obs = intervals#observer#getNonRelationalVariableObserver in
    match (obs v)#getValue with
    | STRIDED_INTERVAL_VAL i -> i
    | _ -> topStridedInterval      
         
  method private reduceIntervalsWRT cst intervals =
    let factors = cst#getFactorsTable#listOfPairs in
    let constant = cst#getConstant in
    let rec residual l i =
      match l with
      | [] -> mkSingletonStridedInterval constant
      | (f, c) :: l' ->
	 let r = (self#getRange f#getVariable i)#mult (mkSingletonStridedInterval c) in
	 (residual l' i)#sub r
    in
    let rec process l t i =
      match l with
      | [] -> i
      | (f, c) :: l' ->
	 let v = f#getVariable in
	 let new_i = (residual (t @ l') i)#div (mkSingletonStridedInterval c) in
	 let i' = i#importNonRelationalValues
                    ?refine:(Some true) [(v, mkStridedIntervalValue new_i)] in
	 if i'#isBottom then
	   raise Bottom_found
	 else
	   process l' ((f, c) :: t) i'
    in
    process factors [] intervals
    
  method private reduceIntervals csts intervals =
    try
      List.fold_left (fun a cst -> self#reduceIntervalsWRT cst a) intervals csts
    with Bottom_found -> intervals#mkBottom
                       
  method private reduceKarr karr intervals =
    let factors = List.map (fun f -> f#getVariable) karr#observer#getObservedFactors in
    List.fold_left (fun k v -> 
	match (self#getRange v intervals)#singleton with
	| None -> k
	| Some n -> k#importNonRelationalValues
                      ?refine:(Some true) [(v, mkNumericalConstantValue (mkNumericalConstant n))]
      ) karr factors
    
  method private sigma (karr, intervals) =
    let csts =
      List.filter (fun cst ->
          match cst#getKind with
          | LINEAR_EQ -> true | _ -> false)
                  (karr#observer#getNumericalConstraints ~variables:None ()) in
    let intervals' = self#reduceIntervals csts intervals in
      if intervals'#isBottom then
	(karr#mkBottom, intervals#mkBottom)
      else
	let karr' = self#reduceKarr karr intervals' in
	(karr', intervals')
	
end
  

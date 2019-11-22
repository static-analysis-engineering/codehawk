(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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
open CHBounds
open CHCommon
open CHIntervals   
open CHLanguage   
open CHNumerical   
open CHPretty
open CHUtils

module P = Pervasives

class numerical_factor_t ?(index: numerical_t option) ?(tag = "") (v: variable_t)  =
object (_: 'a)

  val variable = v
               
  val index = index
            
  val tag = tag
          
  method getVariable = variable
                     
  method getIndex = index
                  
  method getTag = tag
                
  method tag (t: string) = {< tag = t >}
                         
  method equal (f: 'a) =
    variable#equal f#getVariable &&
      match (index, f#getIndex) with
      | (None, None) -> true
      | (Some i1, Some i2) -> i1#equal i2
      | _ -> false
	   
  method compare (f: 'a) =
    if tag = f#getTag then
      match (index, f#getIndex) with
      | (None, Some _) -> -1
      | (Some _, None) -> 1
      | (Some i1, Some i2) ->
	 if i1#equal i2 then
	   variable#compare f#getVariable
	 else
	   i1#compare i2
      | (None, None) ->
	 variable#compare f#getVariable
    else
      P.compare tag f#getTag
    
  method toPretty =
    LBLOCK [
        if tag = "" then STR "" else LBLOCK [STR tag; STR "*"];
        variable#toPretty;
        match index with
	| Some i -> LBLOCK [STR "["; i#toPretty; STR "]"]
	| None -> STR ""
      ]
      
end

type numerical_constraint_kind_t =
  | LINEAR_EQ        (**   =  *)
  | LINEAR_INEQ      (**  <=  *)
  
  
module FactorCollections =
  CHCollections.Make
    (struct
      type t = numerical_factor_t
      let compare f1 f2 = f1#compare f2
      let toPretty f = f#toPretty
    end)
  
class numerical_constraint_t
        ~(factors: (numerical_t * numerical_factor_t) list)
        ~(constant: numerical_t)
        ~(kind: numerical_constraint_kind_t) =
object (self: 'a)
     
  val mutable normalized = false
                         
  val kind = kind
           
  val mutable constant = constant
                       
  val mutable factors_table =
    let t = new FactorCollections.table_t in
    let _ =
      List.iter (fun (c, f) ->
	  if c#equal numerical_zero then
	    ()
	  else
	    t#set f c) factors
    in
    t
    
  method isNormalized = normalized
                      
  method getKind = kind
                 
  method getConstant = constant
                     
  method getFactorsTable = factors_table
                         
  method normalize ?(pivot: numerical_factor_t option) () =
    if normalized then
      ()
    else
      let _ = normalized <- true in
      let gcd = factors_table#fold (fun a _ c -> a#gcd c) constant in
      let gcd = if gcd#lt numerical_zero then gcd#neg else gcd in
      let factors_table' = factors_table#map (fun c -> c#div gcd) in
      let constant' = constant#div gcd in
      let (factors_table'', constant'') =
	match pivot with
	| None -> (factors_table', constant')
	| Some p ->
	   begin
	     match factors_table#get p with
	     | None -> (factors_table', constant')
	     | Some c_p ->
                if c_p#geq numerical_zero then
		  (factors_table', constant')
		else
		  (factors_table'#map (fun c ->
                       c#mult numerical_one#neg), constant'#mult numerical_one#neg)
	   end
      in
      begin
        factors_table <- factors_table'';
        constant <- constant''
      end
      
  method getCoefficient f =
    match factors_table#get f with
    | None -> numerical_zero
    | Some c -> c
              
  method getFactors =
    factors_table#fold (fun a f _ -> f :: a) []
    
  method getFactorsList =
    factors_table#fold (fun a f c -> (c, f) :: a) []
    
  method getVariablesList =
    List.map (fun f -> f#getVariable) factors_table#keys#toList
    
  method getVariables =
    let vars = new VariableCollections.set_t in
    let _ = factors_table#keys#iter (fun f -> vars#add f#getVariable) in
    vars
    
  method isContradiction = 
    match kind with
    | LINEAR_EQ ->
       factors_table#size = 0 && not(constant#equal numerical_zero)
    | LINEAR_INEQ ->
       factors_table#size = 0 && constant#lt numerical_zero
      
  method isTrivial = 
    match kind with
    | LINEAR_EQ ->
       factors_table#size = 0 && constant#equal numerical_zero
    | LINEAR_INEQ ->
       factors_table#size = 0 && constant#geq numerical_zero
      
  method range =
    match self#getFactorsList with
    | [(k, f)] ->
       (match kind with
	| LINEAR_EQ ->
	   Some (f#getVariable, (mkSingletonInterval constant)#div (mkSingletonInterval k))
	| LINEAR_INEQ ->
	   Some (f#getVariable,
                 (new interval_t
                      (new bound_t MINUS_INF)
                      (new bound_t (NUMBER constant)))#div (mkSingletonInterval k))
       )
    | _ ->
       None
      
  method equal (cst: 'a) =
    self#normalize ();
    cst#normalize ();
    let factors = new FactorCollections.set_t in
    let factors' = new FactorCollections.set_t in
    let _ = factors#addList factors_table#listOfKeys in
    let _ = factors'#addList cst#getFactorsTable#listOfKeys in
    factors#equal factors' && constant#equal cst#getConstant &&
      try
	factors_table#iter (fun f coeff ->
	    if coeff#equal (cst#getCoefficient f) then
	      ()
	    else
	      raise Found);
	true
      with Found -> false
                  
  method affineCombination a b (cst: 'a) =
    match kind with
    | LINEAR_EQ ->
       let t = new FactorCollections.table_t in
       let factors = new FactorCollections.set_t in
       let _ = factors#addList factors_table#listOfKeys in
       let _ = factors#addList cst#getFactorsTable#listOfKeys in
       let _ =
         factors#iter (fun f -> 
	     let c = ((self#getCoefficient f)#mult a)#add ((cst#getCoefficient f)#mult b) in
	     if c#equal numerical_zero then
	       ()
	     else
	       t#set f c) in
       {< factors_table = t;
          normalized = false;
          constant = (constant#mult a)#add (cst#getConstant#mult b)
       >}
    | _ ->
       raise (CHFailure (STR "Affine combination can be applied to linear equality constraints only"))
      
  method increment f n =
    let c = self#getCoefficient f in
    if c#equal numerical_zero then
      {< >}
    else
      {< normalized = false; constant = constant#add (c#mult n)>}
    
  method toPretty =
    let pp_coeff first c =
      if c#equal numerical_one then
	if first then 
	  STR "" 
	else 
	  STR "+"
      else if c#equal numerical_one#neg then
	STR "-"
      else if c#lt numerical_zero then
	c#toPretty
      else
	LBLOCK [(if first then STR "" else STR "+"); c#toPretty]
    in
    self#normalize ();
    let (lhs, _) = factors_table#fold
                     (fun (a, first) f c ->
                       ((LBLOCK [pp_coeff first c; f#toPretty]) :: a, false)) ([], true) in
    LBLOCK [LBLOCK (List.rev lhs);
	    (match kind with
	     | LINEAR_EQ -> STR " = "
	     | LINEAR_INEQ -> STR " <= ");
	    constant#toPretty]
    
end
  

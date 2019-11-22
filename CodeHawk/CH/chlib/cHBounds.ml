(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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
  ------------------------------------------------------------------------------ *)

(* chlib *)
open CHCommon
open CHNumerical   
open CHPretty


type bounds_t = 
  | MINUS_INF
  | PLUS_INF
  | NUMBER of numerical_t
            
type polarity_t =
  | POS
  | NEG
  | BOTH
  
class bound_t (b: bounds_t) =
object (self: 'a)
     
  val bound = b
            
  method private mkNew b =
    {< bound = b >}
    
  method getBound = bound
                  
  method equal (a: 'a) =
    match (bound, a#getBound) with
    | (MINUS_INF, MINUS_INF) -> true
    | (PLUS_INF, PLUS_INF) -> true
    | (NUMBER x, NUMBER y) -> x#equal y
    | (_, _) -> false
	      
  method leq (a: 'a) =
    match (bound, a#getBound) with
    | (MINUS_INF, _) -> true
    | (_, PLUS_INF) -> true
    | (NUMBER x, NUMBER y) -> x#leq y
    | (_, _) -> false
              
  method geq (a: 'a) = a#leq self
    
  method lt (a: 'a) = self#leq a && not(self#equal a)
    
  method gt (a: 'a) = a#lt self
    
  method isInfinite =
    match bound with
    | PLUS_INF | MINUS_INF -> true
    | _ -> false
         
  method min (a: 'a) = if self#leq a then self else a

  method max (a: 'a) = if self#leq a then a else self

  method add (a: 'a) =
    match (bound, a#getBound) with
    | (PLUS_INF, _) -> self#mkNew PLUS_INF
    | (_, PLUS_INF) -> self#mkNew PLUS_INF
    | (MINUS_INF, _) -> self#mkNew MINUS_INF
    | (_, MINUS_INF) -> self#mkNew MINUS_INF
    | (NUMBER x, NUMBER y) -> self#mkNew (NUMBER (x#add y))
                            
  method sub (a: 'a) = self#add a#neg
    
  method neg =
    match bound with
    | PLUS_INF -> self#mkNew MINUS_INF
    | MINUS_INF -> self#mkNew PLUS_INF
    | NUMBER x -> self#mkNew (NUMBER (numerical_zero#sub x))
                
  method mult (a: 'a) =
    match (bound, a#getBound) with
    | (PLUS_INF, PLUS_INF) -> self#mkNew PLUS_INF
    | (PLUS_INF, MINUS_INF) -> self#mkNew MINUS_INF
    | (PLUS_INF, NUMBER x) -> 
       if x#equal numerical_zero then 
	 self#mkNew (NUMBER numerical_zero)
       else if x#gt numerical_zero then 
	 self#mkNew PLUS_INF 
       else 
	 self#mkNew MINUS_INF
    | (MINUS_INF, _) ->
       ((self#mkNew PLUS_INF)#mult (self#mkNew a#getBound))#neg
    | (NUMBER x, NUMBER y) -> 
       self#mkNew (NUMBER (x#mult y))
    | (NUMBER _, _) -> 
       a#mult self
      
  method div_floor (a: 'a) =
    let r = match (bound, a#getBound) with
      | (PLUS_INF, PLUS_INF) -> PLUS_INF
      | (MINUS_INF, MINUS_INF) -> PLUS_INF
      | (PLUS_INF, MINUS_INF) -> MINUS_INF
      | (MINUS_INF, PLUS_INF) -> MINUS_INF
      | (PLUS_INF, NUMBER x) -> if x#geq numerical_zero then PLUS_INF else MINUS_INF
      | (MINUS_INF, NUMBER x) -> if x#geq numerical_zero then MINUS_INF else PLUS_INF
      | (NUMBER n, NUMBER d) -> NUMBER (n#toRational#div d#toRational)#floor
      | (NUMBER _, _) -> NUMBER numerical_zero
    in
    self#mkNew r
    
  method div_ceiling (a: 'a) =
    let r = match (bound, a#getBound) with
      | (PLUS_INF, PLUS_INF) -> PLUS_INF
      | (MINUS_INF, MINUS_INF) -> PLUS_INF
      | (PLUS_INF, MINUS_INF) -> MINUS_INF
      | (MINUS_INF, PLUS_INF) -> MINUS_INF
      | (PLUS_INF, NUMBER x) -> if x#geq numerical_zero then PLUS_INF else MINUS_INF
      | (MINUS_INF, NUMBER x) -> if x#geq numerical_zero then MINUS_INF else PLUS_INF
      | (NUMBER n, NUMBER d) -> NUMBER (n#toRational#div d#toRational)#ceiling
      | (NUMBER _, _) -> NUMBER numerical_zero
    in
    self#mkNew r
    
  method toPretty =
    match bound with
    | PLUS_INF -> STR "+oo"
    | MINUS_INF -> STR "-oo"
    | NUMBER x -> x#toPretty
	        
  method polarity (a: 'a) =
    let zero = self#mkNew (NUMBER numerical_zero) in
    if zero#leq self then
      POS
    else if a#lt zero then
      NEG
    else
      BOTH
    
    
  method toNumber =
    match bound with
    | NUMBER x -> x
    | _ -> raise (CHFailure (STR "Bound is not a number"))
         
end
  
let minus_inf_bound = new bound_t MINUS_INF
                    
let plus_inf_bound = new bound_t PLUS_INF
                   
let bound_of_num n = new bound_t (NUMBER n)
                   
let min_in_bounds l =
  match l with
  | [] -> plus_inf_bound
  | b :: l' -> List.fold_left (fun m x -> if x#lt m then x else m) b l'
             
let max_in_bounds l =
  match l with
  | [] -> minus_inf_bound
  | b :: l' -> List.fold_left (fun m x -> if x#gt m then x else m) b l'
             

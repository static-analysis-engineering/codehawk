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
open CHBounds
open CHCommon
open CHNumerical   
open CHPretty


class interval_t min_i max_i =
object (self : 'a)
     
  val bottom = max_i#lt min_i
             
  val min = min_i
          
  val max = max_i
          
  method isBottom = bottom
                  
  method getMin = min
                
  method getMax = max
                
  method clone = {< >}
               
  method toPretty =
    if bottom then
      STR "_|_"
    else
      LBLOCK [STR "["; min#toPretty; STR "; "; max#toPretty; STR "]"]	
    
  method mkBottom = {< bottom = true >}
                  
  method mkTop =
    {< bottom = false; min = new bound_t MINUS_INF; max = new bound_t PLUS_INF >}
    
  method mkInterval min' max' =
    let bottom' = max'#lt min' in
    {< min = min'; max = max'; bottom = bottom' >}
    
  method isTop =
    min#equal (new bound_t MINUS_INF) && max#equal (new bound_t PLUS_INF)
    
  method isBounded = not(min#isInfinite || max#isInfinite)    
                   
  method equal (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, true) -> true
    | (false, false) -> min#equal a#getMin && max#equal a#getMax
    | (_, _) -> false
	      
  method leq (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> true
    | (_, true) -> false
    | (false, false) -> a#getMin#leq min && max#leq a#getMax
                      
  method meet (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) ->
       self#mkInterval (min#max a#getMin) (max#min a#getMax)
      
  method join (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> a#clone
    | (_, true) -> self#clone
    | (false, false) -> 
       self#mkInterval (min#min a#getMin) (max#max a#getMax)
      
  method widening (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#clone
    | (false, false) ->
       self#mkInterval (if a#getMin#lt min then new bound_t MINUS_INF else min)
	               (if max#lt a#getMax then new bound_t PLUS_INF else max)
      
  method narrowing (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
      | (false, false) ->
	 self#mkInterval (if min#equal (new bound_t MINUS_INF) then a#getMin else min)
	                 (if max#equal (new bound_t PLUS_INF) then a#getMax else max)
	
  method upperBound (b: bound_t) =
    match b#getBound with
    | NUMBER _ -> self#meet (self#mkInterval (new bound_t MINUS_INF) b)
    | _ -> {< >}
         
  method strictUpperBound (b: bound_t) =
    match b#getBound with
    | NUMBER _ ->
       self#meet
         (self#mkInterval (new bound_t MINUS_INF)
                          (b#sub (new bound_t (NUMBER numerical_one))))
    | _ -> {< >}
         
  method lowerBound (b: bound_t) =
    match b#getBound with 
    | NUMBER _ -> self#meet (self#mkInterval b (new bound_t PLUS_INF))
    | _ -> {< >}
	 
  method strictLowerBound (b: bound_t) =
    match b#getBound with
    | NUMBER _ ->
       self#meet (self#mkInterval (b#add (new bound_t (NUMBER numerical_one)))
                                  (new bound_t PLUS_INF))
    | _ -> {< >}
         
  method add (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) ->
       self#mkInterval (min#add a#getMin) (max#add a#getMax)
      
  method neg =
    if bottom then
      self#mkBottom
    else
      self#mkInterval (max#neg) (min#neg)
    
  method sub (a: 'a) =
    self#add (a#neg)
    
  method mult (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) ->
       begin
	 match (min#polarity max, a#getMin#polarity a#getMax) with
	   (POS, POS) ->
	   self#mkInterval (min#mult a#getMin) (max#mult a#getMax)
	 | (POS, NEG) ->
	    self#mkInterval (max#mult a#getMin)  (a#getMax#mult min)
	 | (POS, BOTH) ->
	    self#mkInterval (max#mult a#getMin) (max#mult a#getMax)
	 | (NEG, _) ->
	    (self#neg#mult a)#neg
	 | (BOTH, POS) ->
	    a#mult self
	 | (BOTH, NEG) ->
	    a#mult self
	 | (BOTH, BOTH) ->
	    let rmin = (min#mult a#getMax)#min (a#getMin#mult max) in
	    let rmax = (min#mult a#getMin)#min (max#mult a#getMax) in
	    self#mkInterval rmin rmax
       end
      
  method div (i: 'a) =
    match (bottom, i#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) ->
       if i#contains numerical_zero then
	 self#mkInterval minus_inf_bound plus_inf_bound
       else
	 let (a, b) = (self#getMin, self#getMax) in
	 let (a', b') = (i#getMin, i#getMax) in
	 let min_l = [a#div_floor a'; a#div_floor b'; b#div_floor a'; b#div_floor b'] in 
	 let max_l = [a#div_ceiling a'; a#div_ceiling b'; b#div_ceiling a'; b#div_ceiling b'] in 
	 (* If we deal only with integers then min is ceiling and max is floor *)
         (*	    let min_l = [a#div_ceiling a'; a#div_ceiling b'; b#div_ceiling a'; b#div_ceiling b'] in *)
         (*          let max_l = [a#div_floor a'; a#div_floor b'; b#div_floor a'; b#div_floor b'] in *)
	 self#mkInterval (min_in_bounds min_l) (max_in_bounds max_l)
         
  method singleton =
    if bottom then
      None
    else if min#equal max then
      match min#getBound with
      | NUMBER n -> Some n
      | _ -> None 
    else
      None
    
  method iter (f: numerical_t -> unit) =
    let rec loop i stop =
      if i#gt stop then
	()
      else
	begin
	  f i;
	  loop (i#add numerical_one) stop
	end
    in
    match (min#getBound, max#getBound) with
    | (NUMBER start, NUMBER stop) -> loop start stop
    | _ -> raise (CHFailure (STR "Iterating on an unbounded interval"))
         
  method contains n =
    if bottom then
      false
    else
      let b = new bound_t (NUMBER n) in
      min#leq b && b#leq max
      
end
  
let mkSingletonInterval n =
  let bound = new bound_t (NUMBER n) in
  new interval_t bound bound
  
let topInterval = 
  new interval_t (new bound_t MINUS_INF) (new bound_t PLUS_INF)
  
let bottomInterval = 
  new interval_t (new bound_t PLUS_INF) (new bound_t MINUS_INF)
  
let mkInterval min max =
  new interval_t (new bound_t (NUMBER min)) (new bound_t (NUMBER max))
  
  

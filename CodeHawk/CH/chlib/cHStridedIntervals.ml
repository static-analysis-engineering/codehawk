(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Anca Browne
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

(* 
 * The class implements sets of the type { a <= stride * x + rem <= b | x integer } 
 * where a, b, rem, stride are integer constants such that 0 <= rem < stride.
 * If a set contains all the integers between a and b, then stride = 1 and rem = 0. 
 * (This is the case for bottom, top, and singleton sets.)
 *)

open Big_int_Z

(* chlib *)
open CHCommon
open CHNumerical
open CHBounds
open CHPretty
open CHIntervals

(* ensures min is reachable with stride *)
let adjustMin (mn: bound_t) (ms: numerical_t) (mr: numerical_t) : bound_t =                                      
  match mn#getBound with
  | NUMBER mnn -> 
     let stride_of_mnn = (mnn#add (ms#sub (mr#add numerical_one)))#div ms in 
     bound_of_num ((stride_of_mnn#mult ms)#add mr)
  | _ -> mn;;

(* ensures max is reachable with stride *)
let adjustMax (mx: bound_t) (ms: numerical_t) (mr: numerical_t) : bound_t =                                     
  match mx#getBound with
  | NUMBER mxn -> 
     let stride_of_mxn = (mxn#sub mr)#div ms in bound_of_num ((stride_of_mxn#mult ms)#add mr)
  | _ -> mx;;

(* assumes mn, mx are reachable with stride *)
let isBottom (mn: bound_t) (mx: bound_t) : bool =                                           
  match (mn#getBound, mx#getBound) with
  | (PLUS_INF, _ ) -> true
  | (_, MINUS_INF) -> true
  | (_,_) -> mx#lt mn;;

(* assumes mn, mx are reachable with the stride; ensures stride >= 1 *)
let adjustStride (mn: bound_t) (mx: bound_t) (st: numerical_t) : numerical_t =
  if (mx#leq mn) then numerical_one else st
  
(* assumes mn, mx are reachable with the stride; ensures rem < stride *)
let adjustRem (_mn: bound_t) (_mx: bound_t) (st: numerical_t) (rm: numerical_t) : numerical_t =                                     
  if (st#equal numerical_one) then numerical_zero else rm#modulo st
  
  
(* solve ax - by = c (where a and b are relatively prime and a > b ) over integers; returns (x,y) *)
let diophantine (a: big_int) (b: big_int) (c: big_int) : big_int * big_int =                                         
  let rec rdiophantine
            (a: big_int) (b: big_int) 
            (m1: big_int) (m2: big_int) (n1: big_int) (n2: big_int):big_int * big_int = 
    let (q,r) = quomod_big_int a b in
    if (eq_big_int r zero_big_int) 
    then (m2,n2)   
    else 
      let new_a = b and
	  new_b = r and
	  new_m1 = m2 and
	  new_m2 = add_big_int (mult_big_int q m2) m1 and
	  new_n1 = n2 and
	  new_n2 = add_big_int (mult_big_int q n2) n1 in
      rdiophantine new_a new_b new_m1 new_m2 new_n1 new_n2 in
  let (y,x) = rdiophantine a b zero_big_int unit_big_int unit_big_int zero_big_int in
  let det = sub_big_int (mult_big_int a x) (mult_big_int b y) in
  let d = div_big_int c det
  in
  (mult_big_int x d, mult_big_int y d)                          
  
(* returns x positive such that ax - by = c for some y *)
let prediophantine (a: big_int) (b: big_int) (c: big_int) : big_int =                                          
  if (lt_big_int a b)
  then snd (diophantine b a (minus_big_int c))
  else fst (diophantine a b c)
  
(* implementation of {x: x in [min,max] such that x = rem (mod stride)}  *) 
class strided_interval_t (min_i:bound_t) (max_i:bound_t) (stride_i:numerical_t) (rem_i:numerical_t) =
object (self : 'a)
     
  val min: bound_t = min_i   (* mkInterval ensures that min is in the set *)
                   
  val max: bound_t = max_i   (* mkInterval ensures that max is in the set *)
	           
  val bottom: bool = 
     isBottom min_i max_i    (* true when the set is empty *)
    
  val stride: numerical_t = stride_i (* stride >= 1; 1 - no integers are excluded from the interval *)
                          
  val rem: numerical_t = rem_i  (* rem < stride *)
                       
  method isBottom : bool = bottom
                         
  method getMin : bound_t = min
                          
  method getMax : bound_t = max
                          
  method getStride : numerical_t = stride
                                 
  method getRem : numerical_t = rem
                              
  method clone : 'a = {< >}
                    
  method isSingleton : bool = 
    match (min#getBound,max#getBound) with 
    | (NUMBER x,NUMBER y) -> x#equal y
    | (_,_) -> false
             
  method toPretty : pretty_t =
    if self#isBottom then
      STR "_|_"
    else if self#isSingleton then
      min#toPretty
    else if (stride#equal numerical_one) then
      LBLOCK [STR "["; min#toPretty; STR "; "; max#toPretty; STR "]"]
    else if (rem#equal numerical_zero) then
      LBLOCK [STR "{"; min#toPretty; STR " <= "; stride#toPretty; STR "x";
              STR " <= "; max#toPretty; STR "}"]
    else
      LBLOCK [STR "{"; min#toPretty; STR " <= "; stride#toPretty;
              STR "x + "; rem#toPretty; STR " <= "; max#toPretty; STR "}"]
    
  method mkBottom : 'a = 
    {< bottom = true >}
    
  method mkTop : 'a = 
    {< bottom = false;
       min = new bound_t MINUS_INF;
       max = new bound_t PLUS_INF;
       stride = numerical_one;
       rem = numerical_zero >}
    
  (* assures all the above properties of the values *)
  method mkInterval (min': bound_t) (max': bound_t) (stride': numerical_t) (rem': numerical_t) : 'a = 
    if min'#gt max' then self#mkBottom 
    else 
      let mn = adjustMin min' stride' rem' and
          mx = adjustMax max' stride' rem' in
      let st = adjustStride mn mx stride' in
      let rm = adjustRem mn mx st rem' in
      let bt = mx#lt mn in 
      {< min = mn; max = mx; bottom = bt; stride = st; rem = rm >}
      
  method mkSingleton (n: numerical_t) : 'a = 
    let bound = NUMBER n in
    {<min = new bound_t bound;
      max = new bound_t bound;
      bottom = false;
      stride = numerical_one;
      rem = numerical_zero>}
    
  (* assures all the above properties of its own values *)
  method adjust : 'a = 
    self#mkInterval min max stride rem
    
  method isTop : bool =
    min#equal (new bound_t MINUS_INF) && max#equal (new bound_t PLUS_INF) && (stride#equal numerical_one)
    
  method equal (a: 'a) =
    match (bottom, a#isBottom) with
    | (true, true) -> true
    | (false, false) -> 
       min#equal a#getMin && max#equal a#getMax && 
         stride#equal a#getStride && rem#equal a#getRem 
    | (_, _) -> false
              
  method isInInterval (x:numerical_t) : bool = 
    (not bottom) && min#leq (new bound_t (NUMBER x)) && max#geq (new bound_t (NUMBER x))
    
  method isBoundInInterval (b: bound_t) : bool = 
    match (min#getBound, max#getBound, b#getBound) with
    | (NUMBER mn, NUMBER mx, NUMBER x) -> (x#geq mn) && (x#leq mx)
    | (NUMBER _mn, NUMBER _mx, _) -> false
    | (NUMBER mn, PLUS_INF, NUMBER x) -> x#geq mn
    | (NUMBER _mn, PLUS_INF, PLUS_INF) -> true
    | (MINUS_INF, NUMBER mx, NUMBER x) -> x#leq mx
    | (MINUS_INF, NUMBER _mx, MINUS_INF) -> true
    | (MINUS_INF, PLUS_INF, _) -> true
    | (_,_,_) -> false
               
  (* For a non-empty interval, checks that x - rem is a multiple of stride.
     It does not check the bounds. It assumes that the stride is not 0 *)
  method isInStrideWithRem (x:numerical_t) : bool = 
    let isInStrWithRem x = 
      let y = x#sub rem in
      let z = y#modulo stride in
      z#is_zero in
    (not bottom) && (isInStrWithRem x)
    
  method singleton : numerical_t option =
    if bottom then
      None
    else if min#equal max then
      match min#getBound with
      | NUMBER n -> Some n
      | _ -> None 
    else
      None
    
  method leq (a: 'a) : bool =
    match (bottom, a#isBottom) with
    | (true, _) -> true
    | (_, true) -> false
    | (false, false) -> 
       a#getMin#leq min && max#leq a#getMax && 
         (a#getStride#is_zero
          || (a#isInStrideWithRem rem && (stride#modulo a#getStride)#is_zero))
      
  method meet (a: 'a) : 'a =
    match (bottom, a#isBottom, self#isSingleton, a#isSingleton, stride#equal a#getStride, rem#equal a#getRem) with
    | (true, _, _, _, _ ,_) -> self#mkBottom
    | (_, true, _, _, _, _) -> self#mkBottom
    | (_, _, true, _, _, _) -> if (a#isBoundInInterval min) then self#clone else self#mkBottom
    | (_, _, _, true, _, _) -> if (self#isBoundInInterval a#getMin) then a#clone else self#mkBottom
    | (_, _, _, _, true, true) -> self#mkInterval (min#max a#getMin) (max#min a#getMax) stride rem
    | (_, _, _, _, true, false) -> self#mkBottom  
    | (_, _, _, _, _, true) ->
       self#mkInterval (min#max a#getMin) (max#min a#getMax) (stride#lcm a#getStride) rem
    | _ -> 
       let g = stride#gcd a#getStride and
           d = a#getRem#sub rem in 
       let m = d#modulo g
       in
       if (m#is_zero) then
         let new_stride = stride#lcm a#getStride and
             s1 = div_big_int stride#getNum g#getNum and
             s2 = div_big_int a#getStride#getNum g#getNum and
             df = div_big_int d#getNum g#getNum in
         let x = prediophantine s1 s2 df in
         let new_rem = new numerical_t (add_big_int (mult_big_int stride#getNum x) rem#getNum)
         in
         self#mkInterval (min#max a#getMin) (max#min a#getMax) new_stride new_rem
       else self#mkBottom
       
  method join (a: 'a) : 'a =
    match (bottom, a#isBottom) with
    | (true, _) -> a#clone
    | (_, true) -> self#clone
    | _ ->
       let new_min = min#min a#getMin and 
           new_max = max#max a#getMax in
       begin 
         match (self#singleton, a#singleton) with
         | (Some x, Some y) ->
            if (x#equal y) then
              self#clone
            else self#mkInterval new_min new_max ((new_max#sub new_min)#toNumber) (new_min#toNumber)
         | (Some x, _) ->
            self#mkInterval new_min new_max ((a#getStride)#gcd (x#sub a#getRem)) (a#getRem)
         | (_, Some y) ->
            self#mkInterval new_min new_max (stride#gcd (y#sub rem)) rem
         | _ ->
            self#mkInterval new_min new_max ((stride#gcd a#getStride)#gcd (rem#sub a#getRem)) rem
       end
       
  method widening (a: 'a) : 'a =
    match (bottom, a#isBottom) with
    | (true, _) -> a#clone                (* WHY IS THIS BOTTOM FOR INTERVALS ? *)
    | (_, true) -> self#clone
    | (false, false) ->
       let j = self#join a in
       let new_min = if j#getMin#lt min then new bound_t MINUS_INF else min
       and new_max = if j#getMax#gt max then new bound_t PLUS_INF else max
       and (new_stride, new_rem) =
         if ((j#getStride#equal stride) && (j#getRem#equal rem)) then
           (stride, rem)
         else
           (numerical_one, numerical_zero) 
       in
       j#mkInterval new_min new_max new_stride new_rem
       
  method narrowing (a: 'a) : 'a =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) ->
       let new_min = if min#equal (new bound_t MINUS_INF) then a#getMin else min and
           new_max = if max#equal (new bound_t PLUS_INF) then a#getMax else max
       in
       self#mkInterval new_min new_max stride rem     (* CHANGE? narrow stride, rem *)
       
  (* If b is a number, intersects with (-inf, b) *)
  method upperBound (b: bound_t) : 'a = 
    match b#getBound with
    | NUMBER _ -> self#meet (self#mkInterval (new bound_t MINUS_INF) b stride rem)
    | _ -> {< >}
         
  (* If b is a number, intersects with (-inf, b-1) *)
  method strictUpperBound (b: bound_t) : 'a =
    match b#getBound with
    | NUMBER _ ->
       self#meet (self#mkInterval (new bound_t MINUS_INF)
                                  (b#sub (new bound_t (NUMBER numerical_one))) stride rem) 
    | _ -> {< >}
         
  (* If b is a number, intersects with (b, +inf) *)
  method lowerBound (b: bound_t) : 'a =
    match b#getBound with 
    | NUMBER _ -> self#meet (self#mkInterval b (new bound_t PLUS_INF) stride rem)
    | _ -> {< >}
	 
  (* If b is a number, intersects with (b+1, +inf) *)
  method strictLowerBound (b: bound_t) =
    match b#getBound with
    | NUMBER _ ->
       self#meet (self#mkInterval (b#add (new bound_t (NUMBER numerical_one)))
                                  (new bound_t PLUS_INF) stride rem)
    | _ -> {< >}
         
  (* Returns the smallest strided interval that contains sums of numbers from self and a *) 
  method add (a: 'a) : 'a =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) -> 
       let new_min = min#add a#getMin
       and new_max = max#add a#getMax
       and new_stride =
         if (self#isSingleton) then
           a#getStride 
         else if (a#isSingleton) then
           stride
         else
           stride#gcd a#getStride           (* stride is zero only if the interval is bottom *)
       and new_rem =
         if (self#isSingleton) then
           a#getRem#add (min#toNumber)       (* singleton intervals have stride 1 and rem = 0 *)
         else if (a#isSingleton) then
           rem#add (a#getMin#toNumber)
         else
           rem#add a#getRem                          
        in
	self#mkInterval new_min new_max new_stride new_rem
        
  method neg : 'a =
    if bottom then
      self#mkBottom
    else if self#isSingleton then
      self#mkInterval (max#neg) (min#neg) stride rem
    else
      self#mkInterval (max#neg) (min#neg) stride (stride#sub rem)
    
  (* Returns the smallest strided interval that contains differences of numbers from self and a *) 
  method sub (a: 'a) : 'a =
    self#add (a#neg)
    
  (* Finds the bounds for an interval that contains products of numbers from self and a *)
  method findMultMinMax (a: 'a) : bound_t * bound_t = 
    match (min#polarity max, a#getMin#polarity a#getMax) with
    | (POS, POS) -> (min#mult a#getMin, max#mult a#getMax)
    | (POS, NEG) -> (max#mult a#getMin, a#getMax#mult min)
    | (POS, BOTH) -> (max#mult a#getMin, max#mult a#getMax)
    | (NEG, _) -> let (mn, mx) = self#neg#findMultMinMax a in (mx#neg, mn#neg)
    | (BOTH, POS) -> (a#getMax#mult min, a#getMax#mult max)
    | (BOTH, NEG) ->  a#findMultMinMax self
    | (BOTH, BOTH) ->
       let rmin = (min#mult a#getMax)#min (a#getMin#mult max) and 
           rmax = (min#mult a#getMin)#min (max#mult a#getMax)
       in (rmin, rmax)
        
  (* Finds the stride for an interval that contains products of numbers from self and a *)
  method findMultStride (a: 'a) = 
    match (self#singleton, a#singleton) with 
    | (Some _, Some _) -> numerical_one
    | (Some x, _) ->
       if (x#equal numerical_zero) then numerical_one else (x#abs)#mult a#getStride 
    | (_, Some y) ->
       if (y#equal numerical_zero) then numerical_one else (y#abs)#mult stride
    | _ -> 
       let gcdz a b = if a#is_zero then b else if b#is_zero then a else a#gcd b in
       let find_new_stride s1 s2 r1 r2 =
         List.fold_left gcdz (s1#mult s2) [s1#mult r2; s2#mult r1] in
       find_new_stride stride a#getStride rem a#getRem
       
  (* Finds the rem for an interval that contains products of numbers from self and a *)
  method findMultRem (a: 'a) mult_stride = 
    match (self#singleton, a#singleton) with 
    | (Some _, Some _) -> numerical_zero
    | (Some x, _) ->  (x#mult a#getRem)#modulo mult_stride
    | (_, Some y) -> (y#mult rem)#modulo mult_stride
    | _ -> (rem#mult a#getRem)#modulo mult_stride
          

  (* Finds the an interval that contains products of numbers from self and a *)
  method mult (a: 'a) : 'a =
    match (bottom, a#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | _ -> 
       let (new_min, new_max) = self#findMultMinMax a in
       let new_stride = self#findMultStride a in
       let new_rem = self#findMultRem a new_stride in
       self#mkInterval new_min new_max new_stride new_rem
       
       
  (* Finds the an interval that contains divisions of numbers from self and a *)
  method div (i: 'a) : 'a =
    match (bottom, i#isBottom) with
    | (true, _) -> self#mkBottom
    | (_, true) -> self#mkBottom
    | (false, false) ->
       if i#contains numerical_zero then
         self#mkTop  (* Not very helpful! *)
       else
	 let min_l =
           [ min#div_floor i#getMin;
             min#div_floor i#getMax;
             max#div_floor i#getMin;
             max#div_floor i#getMax ]
         and max_l =
           [ min#div_ceiling i#getMin;
             min#div_ceiling i#getMax;
             max#div_ceiling i#getMin;
             max#div_ceiling i#getMax  ] in
         let new_min = min_in_bounds min_l
         and new_max = max_in_bounds max_l in
         let (new_stride, new_rem) =
           if (i#isSingleton && (stride#modulo i#getMin#toNumber)#is_zero) then
             (stride#div i#getMin#toNumber, rem#div i#getMin#toNumber)
           else
             (numerical_one, numerical_zero)                   (* Any other useful cases ? *)
         in
	 self#mkInterval new_min new_max new_stride new_rem
      
  (* For a finite interval, it iterates f on all the numbers in the interval. *)
  (* WHERE IS THIS USED ?*)
  method iter (f: numerical_t -> unit) =
    let rec loop i stop =
      if i#gt stop then
	()
      else
	begin
	  f i;
	  loop (i#add rem) stop
	end
    in
    match (min#getBound, max#getBound) with
    | (NUMBER start, NUMBER stop) -> loop start stop
    | _ -> raise (CHFailure (STR "Iterating on an unbounded interval"))
         
  (* Checks whether a number is in the interval *)
  method contains (n: numerical_t) : bool = 
    (self#isInInterval n) && (self#isInStrideWithRem n)
    
  method mkNonstridedInterval : interval_t = 
    new interval_t min max
    
end
  
let mkSingletonStridedInterval (n: numerical_t) : strided_interval_t =
  let bound = new bound_t (NUMBER n) in
  new strided_interval_t bound bound numerical_one numerical_zero
  
let mkSingletonStridedIntervalN (n: int) : strided_interval_t =
  mkSingletonStridedInterval (mkNumerical n)
  
let topStridedInterval : strided_interval_t = 
  new strided_interval_t (new bound_t MINUS_INF) (new bound_t PLUS_INF) numerical_one numerical_zero
  
let bottomStridedInterval : strided_interval_t = 
  new strided_interval_t (new bound_t PLUS_INF) (new bound_t MINUS_INF) numerical_one numerical_zero
  
let mkStridedInterval (min: numerical_t) (max: numerical_t) (stride: numerical_t) (rem: numerical_t) : strided_interval_t = 
  let sInt =  new strided_interval_t (new bound_t (NUMBER min)) (new bound_t (NUMBER max)) stride rem
  in sInt#adjust
   
let mkStridedIntervalN (min: int) (max: int) (stride: int) (rem: int) :  strided_interval_t = 
  mkStridedInterval (mkNumerical min) (mkNumerical max) (mkNumerical stride) (mkNumerical rem)
  
let intervalToStridedInterval (i: interval_t) : strided_interval_t = 
  new strided_interval_t (i#getMin) (i#getMax) numerical_one numerical_zero
  
let stridedIntervalToInterval (i: strided_interval_t) : interval_t = 
  i#mkNonstridedInterval
  
  

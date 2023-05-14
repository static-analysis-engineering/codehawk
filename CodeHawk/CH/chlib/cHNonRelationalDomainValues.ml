(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
open CHConstants
open CHExternalValues   
open CHIntervals
open CHLanguage   
open CHNumerical
open CHNumericalConstraints
open CHPEPRange   
open CHPEPRTypes   
open CHPretty
open CHStridedIntervals
open CHSymbolicSets   
open CHTIntervals
open CHValueSets


type nr_domain_value_t =
  | NUM_CONSTANT_VAL of numerical_constant_t
  | SYM_CONSTANT_VAL of symbolic_constant_t
  | BOOL_CONSTANT_VAL of boolean_constant_t
  | INTERVAL_VAL of interval_t
  | TINTERVAL_VAL of tinterval_t
  | STRIDED_INTERVAL_VAL of strided_interval_t
  | PEPR_VAL of pepr_value_int
  | VALUESET_VAL of valueset_t
  | SYM_SET_VAL of symbolic_set_t
  | EXTERNAL_VALUE of external_value_int
  | TOP_VAL
  | BOTTOM_VAL
  
let normalize_nr_value v =
  match v with
  | NUM_CONSTANT_VAL n ->
     if n#isTop then
       TOP_VAL
	else if n#isBottom then
       BOTTOM_VAL
     else
       v
  | SYM_CONSTANT_VAL s ->
     if s#isTop then
       TOP_VAL
     else if s#isBottom then
       BOTTOM_VAL
     else
       v
  | BOOL_CONSTANT_VAL b ->
     if b#isTop then
       TOP_VAL
     else if b#isBottom then
       BOTTOM_VAL
     else
       v
  | INTERVAL_VAL n ->
     if n#isTop then
       TOP_VAL
     else if n#isBottom then
       BOTTOM_VAL
     else
       v
  | TINTERVAL_VAL n ->
     if n#isTop then
       TOP_VAL
     else if n#isBottom then
       BOTTOM_VAL
     else
       v
  | STRIDED_INTERVAL_VAL n -> 
     if n#isTop then
       TOP_VAL
     else if n#isBottom then
       BOTTOM_VAL
     else
       v
  | PEPR_VAL n ->
     if n#is_top then
       TOP_VAL
     else if n#is_bottom then
       BOTTOM_VAL
     else
       v
  | VALUESET_VAL n ->
     if n#isTop then
       TOP_VAL
     else if n#isBottom then
       BOTTOM_VAL
     else
       v
  | SYM_SET_VAL s ->
     if s#isTop then
       TOP_VAL
     else if s#isBottom then
       BOTTOM_VAL
     else
       v
  | EXTERNAL_VALUE e ->
     if e#isTop then
       TOP_VAL
	else if e#isBottom then
       BOTTOM_VAL
     else
       v
  | _ ->
     v
    
class non_relational_domain_value_t (v: nr_domain_value_t) =
object (self: 'a)

  val value = normalize_nr_value v
	    
  method getValue = value
                  
  method toPretty =
    match value with
    | NUM_CONSTANT_VAL v -> v#toPretty
    | SYM_CONSTANT_VAL v -> v#toPretty
    | BOOL_CONSTANT_VAL v -> v#toPretty
    | INTERVAL_VAL v -> v#toPretty
    | TINTERVAL_VAL v -> v#toPretty
    | STRIDED_INTERVAL_VAL v -> v#toPretty
    | PEPR_VAL v -> v#toPretty
    | VALUESET_VAL v -> v#toPretty
    | SYM_SET_VAL v -> v#toPretty
    | EXTERNAL_VALUE v -> v#toPretty
    | TOP_VAL -> STR "<TOP>"
    | BOTTOM_VAL -> STR "_|_"
                  
  method private notNormal =
    let _ = raise (CHFailure (STR "Non-relational value is not in normal form")) in ()
                                                                                  
  method isTop =
    match value with
    | TOP_VAL -> true
    | _ -> false

  method isBottom =
    match value with
    | BOTTOM_VAL -> true
    | _ -> false
         
  method leq (v: 'a) =
    match (value, v#getValue) with
    | (BOTTOM_VAL, _) -> true
    | (_, BOTTOM_VAL) -> false
    | (_, TOP_VAL) -> true
    | (TOP_VAL, _) -> false
    | (SYM_CONSTANT_VAL v1, SYM_CONSTANT_VAL v2) -> v1#leq v2
    | (NUM_CONSTANT_VAL v1, NUM_CONSTANT_VAL v2) -> v1#leq v2
    | (BOOL_CONSTANT_VAL v1, BOOL_CONSTANT_VAL v2) -> v1#leq v2
    | (INTERVAL_VAL v1, INTERVAL_VAL v2) -> v1#leq v2
    | (TINTERVAL_VAL v1, TINTERVAL_VAL v2) -> v1#leq v2
    | (STRIDED_INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) -> v1#leq v2
    | (STRIDED_INTERVAL_VAL v1, INTERVAL_VAL v2) ->
       v1#leq (intervalToStridedInterval v2)
    | (INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) ->
       (intervalToStridedInterval v1)#leq v2
    | (PEPR_VAL v1, PEPR_VAL v2) ->
       let r = v1#leq v2 in
       let _ =
         pr_trace 3 [ STR "Iterator#leq: " ; v1#toPretty ; STR " leq " ; v2#toPretty ;
                      STR " ==> " ; STR (if r then "true" else "false") ; NL ] in
       r
    | (VALUESET_VAL v1, VALUESET_VAL v2) -> v1#leq v2
    | (SYM_SET_VAL v1, SYM_SET_VAL v2) -> v1#leq v2
    | (EXTERNAL_VALUE v1, EXTERNAL_VALUE v2) ->
       if v1#kind = v2#kind then
	 v1#leq v2
       else
	 raise (CHFailure (LBLOCK [STR "Comparison of incompatible external values: ";
				   v1#toPretty; STR " and "; v2#toPretty]))
    | (NUM_CONSTANT_VAL v1, INTERVAL_VAL v2) ->
	  begin
	    match v1#getCst with
	    | NUM_CST n -> v2#contains n
	    | _ -> (self#notNormal; false)
	  end
    | (NUM_CONSTANT_VAL v1, STRIDED_INTERVAL_VAL v2) ->
       begin
	 match v1#getCst with
	 | NUM_CST n -> v2#contains n
	 | _ -> (self#notNormal; false)
       end
    | (INTERVAL_VAL v1, NUM_CONSTANT_VAL v2) ->
       begin
	 match v1#singleton with
	 | None -> false
	 | Some n ->
	    begin
	      match v2#getCst with
	      | NUM_CST n' -> n#equal n'
	      | _ -> (self#notNormal; false)
	    end
       end
    | (STRIDED_INTERVAL_VAL v1, NUM_CONSTANT_VAL v2) ->
       begin
	 match v1#singleton with
	 | None -> false
	 | Some n ->
	    begin
	      match v2#getCst with
	      | NUM_CST n' -> n#equal n'
	      | _ -> (self#notNormal; false)
	    end
       end
    | (SYM_CONSTANT_VAL v1, SYM_SET_VAL v2) ->
       begin
	 match v1#getCst with
	 | SYM_CST s -> v2#contains s
	 | _ -> (self#notNormal; false)
       end
    | (SYM_SET_VAL v1, SYM_CONSTANT_VAL v2) ->
       begin
	 match v1#singleton with
	 | None -> false
	 | Some s ->
	    begin
	      match v2#getCst with
	      | SYM_CST s' -> s#equal s'
	      | _ -> (self#notNormal; false)
	    end
       end	  
    | (_, _) -> false
              
  method join (v: 'a) =
    match (value, v#getValue) with
    | (BOTTOM_VAL, _) -> v
    | (_, BOTTOM_VAL) -> {< >}
    | (TOP_VAL, _) -> {< value = TOP_VAL >}
    | (_, TOP_VAL) -> {< value = TOP_VAL >}
    | (SYM_CONSTANT_VAL v1, SYM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (SYM_CONSTANT_VAL (v1#join v2)) >}
    | (NUM_CONSTANT_VAL v1, NUM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (NUM_CONSTANT_VAL (v1#join v2)) >}
    | (BOOL_CONSTANT_VAL v1, BOOL_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (BOOL_CONSTANT_VAL (v1#join v2)) >}
    | (INTERVAL_VAL v1, INTERVAL_VAL v2) ->
       {< value = normalize_nr_value (INTERVAL_VAL (v1#join v2)) >}
    | (PEPR_VAL v1, PEPR_VAL v2) ->
       let r = {< value = normalize_nr_value (PEPR_VAL (v1#join v2)) >} in
       let _ =
         pr_trace 3 [ STR "Iterator#join: " ; v1#toPretty ; STR " join " ;
                      v2#toPretty ; STR " ==> " ; r#toPretty ; NL ] in
       r
    | (TINTERVAL_VAL v1, TINTERVAL_VAL v2) ->
       {< value = normalize_nr_value (TINTERVAL_VAL (v1#join v2)) >}
    | (STRIDED_INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) ->
       {< value = normalize_nr_value (STRIDED_INTERVAL_VAL (v1#join v2)) >}
    | (INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) ->                                 
       {<value = normalize_nr_value
                   (INTERVAL_VAL (v1#join (stridedIntervalToInterval v2)))>}
    | (STRIDED_INTERVAL_VAL v1, INTERVAL_VAL v2) ->
       {<value = normalize_nr_value
                   (STRIDED_INTERVAL_VAL (v1#join (intervalToStridedInterval v2)))>}
    | (SYM_SET_VAL v1, SYM_SET_VAL v2) ->
       {< value = normalize_nr_value (SYM_SET_VAL (v1#join v2)) >}
    | (EXTERNAL_VALUE v1, EXTERNAL_VALUE v2) ->
       if v1#kind = v2#kind then
	 {< value = EXTERNAL_VALUE (v1#join v2) >}
       else
	 raise (CHFailure (LBLOCK [STR "Join of incompatible external values: ";
				   v1#toPretty; STR " and "; v2#toPretty]))	  
    | (NUM_CONSTANT_VAL v1, INTERVAL_VAL v2) ->
       begin
	 match v1#getCst with
	 | NUM_CST n ->
            {< value = normalize_nr_value
                         (INTERVAL_VAL ((mkSingletonInterval n)#join v2)) >}
	 | _ -> (self#notNormal; v)
       end
    | (NUM_CONSTANT_VAL v1, STRIDED_INTERVAL_VAL v2) ->
       begin
	 match v1#getCst with
	 | NUM_CST n ->
            {< value = normalize_nr_value
                         (STRIDED_INTERVAL_VAL ((mkSingletonStridedInterval n)#join v2)) >}
	 | _ -> (self#notNormal; v)
       end
    | (INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> v#join self
    | (STRIDED_INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> v#join self
    | (VALUESET_VAL v1, VALUESET_VAL v2) ->
       {< value = normalize_nr_value (VALUESET_VAL (v1#join v2)) >}
    | (SYM_CONSTANT_VAL v1, SYM_SET_VAL v2) ->
       begin
	 match v1#getCst with
	 | SYM_CST s ->
            {< value = normalize_nr_value
                         (SYM_SET_VAL ((new symbolic_set_t [s])#join v2)) >}
	 | _ -> (self#notNormal; v)
       end
    | (SYM_SET_VAL _, SYM_CONSTANT_VAL _) -> v#join self
    | (_, _) -> {< value = TOP_VAL >}
              
  method widening (v: 'a) =
    match (value, v#getValue) with
    | (BOTTOM_VAL, _) -> v
    | (_, BOTTOM_VAL) -> {< >}
    | (TOP_VAL, _) -> {< value = TOP_VAL >}
    | (_, TOP_VAL) -> {< value = TOP_VAL >}
    | (SYM_CONSTANT_VAL v1, SYM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (SYM_CONSTANT_VAL (v1#widening v2)) >}
    | (NUM_CONSTANT_VAL v1, NUM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (NUM_CONSTANT_VAL (v1#widening v2)) >}
    | (BOOL_CONSTANT_VAL v1, BOOL_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (BOOL_CONSTANT_VAL (v1#widening v2)) >}
    | (INTERVAL_VAL v1, INTERVAL_VAL v2) ->
       {< value = normalize_nr_value (INTERVAL_VAL (v1#widening v2)) >}
    | (PEPR_VAL v1, PEPR_VAL v2) ->
       let r = {< value = normalize_nr_value (PEPR_VAL (v1#widening v2)) >} in
       let _ =
         pr_trace 3 [ STR "Iterator#widening: " ; v1#toPretty ; STR " widening " ;
                      v2#toPretty ; STR " ==> " ; r#toPretty ; NL ] in
       r
    | (TINTERVAL_VAL v1, TINTERVAL_VAL v2) ->
       {< value = normalize_nr_value (TINTERVAL_VAL (v1#widening v2)) >}
    | (STRIDED_INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) ->
       {< value = normalize_nr_value (STRIDED_INTERVAL_VAL (v1#widening v2)) >}
    | (SYM_SET_VAL v1, SYM_SET_VAL v2) ->
       {< value = normalize_nr_value (SYM_SET_VAL (v1#widening v2)) >}
    | (EXTERNAL_VALUE v1, EXTERNAL_VALUE v2) ->
       if v1#kind = v2#kind then
	 {< value = EXTERNAL_VALUE (v1#widening v2) >}
       else
	 raise (CHFailure (LBLOCK [STR "Widening of incompatible external values: ";
				   v1#toPretty; STR " and "; v2#toPretty]))	  
    | (NUM_CONSTANT_VAL v1, INTERVAL_VAL v2) -> self#join v
    | (NUM_CONSTANT_VAL v1, STRIDED_INTERVAL_VAL v2) -> self#join v
    | (INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> v#widening self
    | (STRIDED_INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> v#widening self
    | (VALUESET_VAL v1, VALUESET_VAL v2) ->
       {< value = normalize_nr_value (VALUESET_VAL (v1#widening v2)) >}
    | (SYM_CONSTANT_VAL v1, SYM_SET_VAL v2) -> self#join v
    | (SYM_SET_VAL _, SYM_CONSTANT_VAL _) -> v#widening self
    | (_, _) -> {< value = TOP_VAL >}

  method meet (v: 'a) =
    match (value, v#getValue) with
    | (BOTTOM_VAL, _) -> {< value = BOTTOM_VAL >}
    | (_, BOTTOM_VAL) -> {< value = BOTTOM_VAL >}
    | (TOP_VAL, _) -> v
    | (_, TOP_VAL) -> {< >}
    | (SYM_CONSTANT_VAL v1, SYM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (SYM_CONSTANT_VAL (v1#meet v2)) >}
      | (NUM_CONSTANT_VAL v1, NUM_CONSTANT_VAL v2) ->
	 {< value = normalize_nr_value (NUM_CONSTANT_VAL (v1#meet v2)) >}
      | (BOOL_CONSTANT_VAL v1, BOOL_CONSTANT_VAL v2) ->
	 {< value = normalize_nr_value (BOOL_CONSTANT_VAL (v1#meet v2)) >}
      | (INTERVAL_VAL v1, INTERVAL_VAL v2) ->
	 {< value = normalize_nr_value (INTERVAL_VAL (v1#meet v2)) >}
      | (PEPR_VAL v1, PEPR_VAL v2) ->
         let r = {< value = normalize_nr_value (PEPR_VAL (v1#meet v2)) >} in
         let _ =
           pr_trace 3 [ STR "Iterator#meet: " ; v1#toPretty ; STR " meet " ;
                        v2#toPretty ; STR " ==> " ; r#toPretty ; NL ] in
         r
      | (TINTERVAL_VAL v1, TINTERVAL_VAL v2) ->
	 {< value = normalize_nr_value (TINTERVAL_VAL (v1#meet v2)) >}
      | (STRIDED_INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) ->
	 {< value = normalize_nr_value (STRIDED_INTERVAL_VAL (v1#meet v2)) >}
      | (VALUESET_VAL v1, VALUESET_VAL v2) ->
	 {< value = normalize_nr_value (VALUESET_VAL (v1#meet v2)) >}
      | (SYM_SET_VAL v1, SYM_SET_VAL v2) ->
	 {< value = normalize_nr_value (SYM_SET_VAL (v1#meet v2)) >}
      | (EXTERNAL_VALUE v1, EXTERNAL_VALUE v2) ->
	 if v1#kind = v2#kind then
	   {< value = EXTERNAL_VALUE (v1#meet v2) >}
	 else
	   raise (CHFailure (LBLOCK [STR "Meet of incompatible external values: ";
				     v1#toPretty; STR " and "; v2#toPretty]))	  
      | (NUM_CONSTANT_VAL v1, INTERVAL_VAL v2) ->
	 begin
	   match v1#getCst with
	   | NUM_CST n -> if v2#contains n then {< >} else {< value = BOTTOM_VAL >}
	   | _ -> (self#notNormal; v)
	 end
      | (NUM_CONSTANT_VAL v1, STRIDED_INTERVAL_VAL v2) ->
	 begin
	   match v1#getCst with
	   | NUM_CST n -> if v2#contains n then {< >} else {< value = BOTTOM_VAL >}
	   | _ -> (self#notNormal; v)
	 end
      | (INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> v#meet self
      | (STRIDED_INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> v#meet self
      | (SYM_CONSTANT_VAL v1, SYM_SET_VAL v2) ->
	 begin
	   match v1#getCst with
	   | SYM_CST s -> if v2#contains s then {< >} else {< value = BOTTOM_VAL >}
	   | _ -> (self#notNormal; v)
	 end
      | (SYM_SET_VAL _, SYM_CONSTANT_VAL _) -> v#meet self
      | (_, _) -> {< value = BOTTOM_VAL >}
                
  method narrowing (v: 'a) =
    match (value, v#getValue) with
    | (BOTTOM_VAL, _) -> {< value = BOTTOM_VAL >}
    | (_, BOTTOM_VAL) -> {< value = BOTTOM_VAL >}
    | (TOP_VAL, _) -> v
    | (_, TOP_VAL) -> {< >}
    | (SYM_CONSTANT_VAL v1, SYM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (SYM_CONSTANT_VAL (v1#narrowing v2)) >}
    | (NUM_CONSTANT_VAL v1, NUM_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (NUM_CONSTANT_VAL (v1#narrowing v2)) >}
    | (BOOL_CONSTANT_VAL v1, BOOL_CONSTANT_VAL v2) ->
       {< value = normalize_nr_value (BOOL_CONSTANT_VAL (v1#narrowing v2)) >}
    | (INTERVAL_VAL v1, INTERVAL_VAL v2) ->
       let r = {< value = normalize_nr_value (INTERVAL_VAL (v1#narrowing v2)) >} in
       let _ =
         pr_trace 3 [ STR "Iterator#narrowing: " ; v1#toPretty ; STR " narrowing " ;
                      v2#toPretty ; STR " ==> " ; r#toPretty ; NL ] in
       r
    | (PEPR_VAL v1, PEPR_VAL v2) ->
       let r = {< value = normalize_nr_value (PEPR_VAL (v1#narrowing v2)) >} in
       let _ =
         pr_trace 3 [ STR "Iterator#narrowing: " ; v1#toPretty ; STR " narrowing " ;
                      v2#toPretty ; STR " ==> " ; r#toPretty ; NL ] in
       r
    | (TINTERVAL_VAL v1, TINTERVAL_VAL v2) ->
       {< value = normalize_nr_value (TINTERVAL_VAL (v1#narrowing v2)) >}
    | (STRIDED_INTERVAL_VAL v1, STRIDED_INTERVAL_VAL v2) ->
       {< value = normalize_nr_value (STRIDED_INTERVAL_VAL (v1#narrowing v2)) >}
    | (VALUESET_VAL v1, VALUESET_VAL v2) ->
       {< value = normalize_nr_value (VALUESET_VAL (v1#narrowing v2)) >}
    | (SYM_SET_VAL v1, SYM_SET_VAL v2) ->
       {< value = normalize_nr_value (SYM_SET_VAL (v1#narrowing v2)) >}
    | (EXTERNAL_VALUE v1, EXTERNAL_VALUE v2) ->
       if v1#kind = v2#kind then
	 {< value = EXTERNAL_VALUE (v1#narrowing v2) >}
       else
	 raise (CHFailure (LBLOCK [STR "Narrowing of incompatible external values: ";
				   v1#toPretty; STR " and "; v2#toPretty]))	  
    | (NUM_CONSTANT_VAL v1, INTERVAL_VAL v2) -> self#meet v
    | (NUM_CONSTANT_VAL v1, STRIDED_INTERVAL_VAL v2) -> self#meet v
    | (INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> self#meet v
    | (STRIDED_INTERVAL_VAL _, NUM_CONSTANT_VAL _) -> self#meet v
    | (SYM_CONSTANT_VAL v1, SYM_SET_VAL v2) -> self#meet v
    | (SYM_SET_VAL _, SYM_CONSTANT_VAL _) -> self#meet v
    | (_, _) -> {< value = BOTTOM_VAL >}
              
  method numericalConstant =
    match value with
    | NUM_CONSTANT_VAL n -> 
       begin
	 match n#getCst with
	 | NUM_CST c -> Some c
	 | _ -> (self#notNormal; None)
       end
    | INTERVAL_VAL i -> i#singleton
    | STRIDED_INTERVAL_VAL i -> i#singleton
    | VALUESET_VAL v -> v#zeroOffsetSingleton
    | PEPR_VAL v -> v#singleton
    | _ -> None
         
  method toNumericalConstraints (v: variable_t) =
    match value with
    | NUM_CONSTANT_VAL n ->
       (match n#getCst with
	| NUM_CST c -> 
	   [new numerical_constraint_t
              ~factors:[(numerical_one, new numerical_factor_t v)]
              ~constant:c
              ~kind:LINEAR_EQ]
	| _ -> []
       )
    | INTERVAL_VAL i ->
       let f = new numerical_factor_t v in
       (match i#getMin#getBound with
	| NUMBER n ->
	   [new numerical_constraint_t
              ~factors:[(numerical_one#neg, f)]
              ~constant:n#neg
              ~kind:LINEAR_INEQ]
	| _ -> [])
       @ 	    
	 (match i#getMax#getBound with
	  | NUMBER n ->
	     [new numerical_constraint_t
                ~factors:[(numerical_one, f)]
                ~constant:n
                ~kind:LINEAR_INEQ]
	  | _ -> [])	      
    | TINTERVAL_VAL i ->
       let f = new numerical_factor_t v in
       (match i#getMin#getBound with
	| NUMBER n ->
	   [new numerical_constraint_t
              ~factors:[(numerical_one#neg, f)]
              ~constant:n#neg
              ~kind:LINEAR_INEQ]
	| _ -> [])
       @ 	    
	 (match i#getMax#getBound with
	  | NUMBER n ->
	     [new numerical_constraint_t
                ~factors:[(numerical_one, f)]
                ~constant:n
                ~kind:LINEAR_INEQ]
	  | _ -> [])	      
    | STRIDED_INTERVAL_VAL i ->                      (* This ignores the stride *)
       let f = new numerical_factor_t v in
       (match i#getMin#getBound with
	| NUMBER n ->
	   [new numerical_constraint_t
              ~factors:[(numerical_one#neg, f)]
              ~constant:n#neg
              ~kind:LINEAR_INEQ]
	| _ -> [])
       @ 	    
	 (match i#getMax#getBound with
	  | NUMBER n ->
	     [new numerical_constraint_t
                ~factors:[(numerical_one, f)]
                ~constant:n
                ~kind:LINEAR_INEQ]
	  | _ -> [])	      
    | _ -> []
         
  method toInterval =
    match value with
    | NUM_CONSTANT_VAL c -> 
       begin
	 match c#getCst with
	 | NUM_CST n -> mkSingletonInterval n
	 | NUM_BOTTOM -> bottomInterval
	 | _ -> topInterval
       end
    | INTERVAL_VAL i -> i
    | STRIDED_INTERVAL_VAL i -> stridedIntervalToInterval i
    | VALUESET_VAL v -> 
       if v#isZeroOffset then v#getZeroOffset  else topInterval
    | BOTTOM_VAL -> bottomInterval
    | _ -> topInterval
         
  method toTInterval =
    match value with
    | NUM_CONSTANT_VAL c -> 
       begin
	 match c#getCst with
	 | NUM_CST n -> mkSingletonTInterval n
	 | NUM_BOTTOM -> bottomTInterval
	 | _ -> topTInterval
       end
    | TINTERVAL_VAL i -> i
    | BOTTOM_VAL -> bottomTInterval
    | _ -> topTInterval
         
  method toStridedInterval =
    match value with
    | NUM_CONSTANT_VAL c -> 
       begin
	 match c#getCst with
	 | NUM_CST n -> mkSingletonStridedInterval n
	 | NUM_BOTTOM -> bottomStridedInterval
	 | _ -> topStridedInterval
       end
    | INTERVAL_VAL i -> intervalToStridedInterval i
    | STRIDED_INTERVAL_VAL i -> i
    | BOTTOM_VAL -> bottomStridedInterval
    | _ -> topStridedInterval
         
  method toNumericalConstant =
    match value with
    | INTERVAL_VAL i -> 
       if i#isBottom then
	 bottomNumericalConstant
       else
	 begin
	   match i#singleton with
	   | Some n -> mkNumericalConstant n
	   | None -> topNumericalConstant
	    end
    | STRIDED_INTERVAL_VAL i -> 
       if i#isBottom then
	 bottomNumericalConstant
       else
	 begin
	   match i#singleton with
	   | Some n -> mkNumericalConstant n
	   | None -> topNumericalConstant
	 end
    | NUM_CONSTANT_VAL c -> c
    | BOTTOM_VAL -> bottomNumericalConstant
    | _ -> topNumericalConstant
         
  method toSymbolicConstant =
    match value with
    | SYM_SET_VAL s -> 
       if s#isBottom then
	 bottomSymbolicConstant
       else
	 begin
	   match s#singleton with
	   | Some sym -> mkSymbolicConstant sym
	   | None -> topSymbolicConstant
	 end
    | SYM_CONSTANT_VAL c -> c
    | BOTTOM_VAL -> bottomSymbolicConstant
    | _ -> topSymbolicConstant
         
  method toSymbolicSet =
    match value with
    | SYM_CONSTANT_VAL c -> 
       begin
	 match c#getCst with
	 | SYM_CST s -> new symbolic_set_t [s]
	 | SYM_BOTTOM -> bottomSymbolicSet
	 | _ -> topSymbolicSet
       end
    | SYM_SET_VAL s -> s
    | BOTTOM_VAL -> bottomSymbolicSet
    | _ -> topSymbolicSet
	 
  method toExternalValue =
    match value with
    | EXTERNAL_VALUE s -> s
    | _ -> raise (CHFailure (LBLOCK [STR "Not an external value: "; self#toPretty]))
         
  method toValueSet =
    match value with
    | VALUESET_VAL v -> v
    | BOTTOM_VAL -> bottomValueSet
    | _ -> topValueSet
         
  method toPEPRValue =
    match value with
    | PEPR_VAL v -> v
    | BOTTOM_VAL -> bottom_pepr_value
    | _ -> top_pepr_value
	 
end
  
let topNonRelationalDomainValue = new non_relational_domain_value_t TOP_VAL
                                
let bottomNonRelationalDomainValue = new non_relational_domain_value_t BOTTOM_VAL
                                   
let mkNumericalConstantValue n = new non_relational_domain_value_t (NUM_CONSTANT_VAL n)
                               
let mkSymbolicConstantValue s = new non_relational_domain_value_t (SYM_CONSTANT_VAL s)
                              
let mkBooleanConstantValue b = new non_relational_domain_value_t (BOOL_CONSTANT_VAL b)
                             
let mkIntervalValue i = new non_relational_domain_value_t (INTERVAL_VAL i)
                      
let mkTIntervalValue i = new non_relational_domain_value_t (TINTERVAL_VAL i)
                       
let mkStridedIntervalValue i = new non_relational_domain_value_t (STRIDED_INTERVAL_VAL i)
                             
let mkSymbolicSetValue s = new non_relational_domain_value_t (SYM_SET_VAL s)
                         
let mkValueSetValue v = new non_relational_domain_value_t (VALUESET_VAL v)
                      
                      

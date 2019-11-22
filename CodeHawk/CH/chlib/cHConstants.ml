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
open CHCommon
open CHLanguage   
open CHNumerical   
open CHPretty
open CHUtils


type num_cst_t =
  | NUM_BOTTOM
  | NUM_CST of numerical_t
  | NUM_TOP
  
class numerical_constant_t (n: num_cst_t) =
object (self: 'a)
     
  val cst = n
          
  method getCst = cst
                
  method private mkNew n =
    {< cst = n >}
    
  method mkTop = {< cst = NUM_TOP >}
               
  method mkBottom = {< cst = NUM_BOTTOM >}
                  
  method isTop =
    match cst with
    | NUM_TOP -> true
    | _ -> false
         
  method isBottom =
    match cst with
    | NUM_BOTTOM -> true
    | _ -> false
         
  method equal (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_BOTTOM, NUM_BOTTOM) -> true
    | (NUM_TOP, NUM_TOP) -> true
    | (NUM_CST c1, NUM_CST c2) -> c1#equal c2
    | (_, _) -> false 
              
  method leq (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_BOTTOM, _) -> true
    | (_, NUM_TOP) -> true
    | (NUM_CST c1, NUM_CST c2) -> c1#equal c2
    | (_, _) -> false
              
  method join (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_TOP, _) -> {< >}
    | (_, NUM_TOP) -> c
    | (NUM_BOTTOM, _) -> c
    | (_, NUM_BOTTOM) -> {< >}
    | (NUM_CST c1, NUM_CST c2) ->
       if c1#equal c2 then
	 c
       else
	 self#mkNew NUM_TOP
      
  method meet (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_TOP, _) -> c
    | (_, NUM_TOP) -> {< >}
    | (NUM_BOTTOM, _) -> {< >}
    | (_, NUM_BOTTOM) -> c
    | (NUM_CST c1, NUM_CST c2) ->
       if c1#equal c2 then
	 c
       else
	 self#mkNew NUM_BOTTOM
      
  method widening = self#join
                  
  method narrowing = self#meet
                   
  method add (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_BOTTOM, _) -> {< >}
    | (_, NUM_BOTTOM) -> c
    | (NUM_CST c1, NUM_CST c2) -> self#mkNew (NUM_CST (c1#add c2))
    | (_, _) -> self#mkNew NUM_TOP
              
  method sub (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_BOTTOM, _) -> {< >}
    | (_, NUM_BOTTOM) -> c
    | (NUM_CST c1, NUM_CST c2) -> self#mkNew (NUM_CST (c1#sub c2))
    | (_, _) -> self#mkNew NUM_TOP
              
  method mult (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_BOTTOM, _) -> {< >}
    | (_, NUM_BOTTOM) -> c
    | (NUM_CST c1, NUM_CST c2) -> self#mkNew (NUM_CST (c1#mult c2))
    | (_, _) -> self#mkNew NUM_TOP
	      
  method div (c: 'a) =
    match (cst, c#getCst) with
    | (NUM_BOTTOM, _) -> {< >}
    | (_, NUM_BOTTOM) -> c
    | (_, _) -> self#mkNew NUM_TOP
              
  method toPretty =
    match cst with
    | NUM_BOTTOM -> STR "_|_"
    | NUM_TOP -> STR "T"
    | NUM_CST c -> c#toPretty
                 
end
  
type sym_cst_t =
  | SYM_BOTTOM
  | SYM_CST of symbol_t
  | SYM_TOP
  
class symbolic_constant_t (s: sym_cst_t) =
object (self: 'a)
     
  val cst = s
          
  method getCst = cst
                
  method private mkNew s =
    {< cst = s >}
    
  method mkTop = {< cst = SYM_TOP >}
               
  method mkBottom = {< cst = SYM_BOTTOM >}
                  
  method isTop =
    match cst with
    | SYM_TOP -> true
    | _ -> false
         
  method isBottom =
    match cst with
    | SYM_BOTTOM -> true
    | _ -> false
         
  method equal (c: 'a) =
    match (cst, c#getCst) with
    | (SYM_BOTTOM, SYM_BOTTOM) -> true
    | (SYM_TOP, SYM_TOP) -> true
    | (SYM_CST s1, SYM_CST s2) -> s1#equal s2
    | (_, _) -> false 
              
  method leq (c: 'a) =
    match (cst, c#getCst) with
    | (SYM_BOTTOM, _) -> true
    | (_, SYM_TOP) -> true
    | (SYM_CST s1, SYM_CST s2) -> s1#equal s2
    | (_, _) -> false
              
  method join (c: 'a) =
    match (cst, c#getCst) with
    | (SYM_TOP, _) -> {< >}
    | (_, SYM_TOP) -> c
    | (SYM_BOTTOM, _) -> c
    | (_, SYM_BOTTOM) -> {< >}
    | (SYM_CST s1, SYM_CST s2) ->
       if s1#equal s2 then
	 c
       else
	 self#mkNew SYM_TOP
      
  method meet (c: 'a) =
    match (cst, c#getCst) with
    | (SYM_TOP, _) -> c
    | (_, SYM_TOP) -> {< >}
    | (SYM_BOTTOM, _) -> {< >}
    | (_, SYM_BOTTOM) -> c
    | (SYM_CST s1, SYM_CST s2) ->
       if s1#equal s2 then
	 c
       else
	 self#mkNew SYM_BOTTOM
      
  method widening = self#join
                  
  method narrowing = self#meet
                   
  method toPretty =
    match cst with
    | SYM_BOTTOM -> STR "_|_"
    | SYM_TOP -> STR "T"
    | SYM_CST s -> s#toPretty
                 
end
  
type bool_cst_t =
  | BOOL_BOTTOM
  | BOOL_CST of bool
  | BOOL_TOP
  
class boolean_constant_t (b:bool_cst_t) =
object (self: 'a)
     
  val cst = b
          
  method getCst = cst
                
  method private mkNew b =
    {< cst = b >}
    
  method mkTop = {< cst = BOOL_TOP >}
               
  method mkBottom = {< cst = BOOL_BOTTOM >}
                  
  method isTop =
    match cst with
    | BOOL_TOP -> true
    | _ -> false
         
  method isBottom =
    match cst with
    | BOOL_BOTTOM -> true
    | _ -> false
         
  method equal (c: 'a) =
    match (cst, c#getCst) with
    | (BOOL_BOTTOM, BOOL_BOTTOM) -> true
    | (BOOL_TOP, BOOL_TOP) -> true
    | (BOOL_CST b1, BOOL_CST b2) -> (b1 = b2)
    | _ -> false
         
  method leq (c: 'a) =
    match (cst, c#getCst) with
    | (BOOL_BOTTOM, _) -> true
    | (_, BOOL_TOP) -> true
    | (BOOL_CST false, BOOL_CST _) -> true
    | (BOOL_CST true, BOOL_CST true) -> true
    | _ -> false
         
  method join (c: 'a) =
    match (cst, c#getCst) with
    | (BOOL_TOP, _) -> {< >}
    | (_, BOOL_TOP) -> c
    | (BOOL_BOTTOM, _) -> c
    | (_, BOOL_BOTTOM) -> {< >}
    | (BOOL_CST b1, BOOL_CST b2) -> 
       self#mkNew (BOOL_CST (b1 || b2))
      
  method meet (c: 'a) =
    match (cst, c#getCst) with
    | (BOOL_TOP, _) -> c
    | (_, BOOL_TOP) -> {< >}
    | (BOOL_BOTTOM, _) -> {< >}
    | (_, BOOL_BOTTOM) -> c
    | (BOOL_CST b1, BOOL_CST b2) ->
       self#mkNew (BOOL_CST (b1 && b2))
      
  method widening = self#join
                  
  method narrowing = self#meet
                   
  method toPretty =
    match cst with
    | BOOL_BOTTOM -> STR "_|_"
    | BOOL_TOP -> STR "T"
    | BOOL_CST b -> 
       if b then (STR "true") else (STR "false")
      
end
  
let mkNumericalConstant n = new numerical_constant_t (NUM_CST n)

let topNumericalConstant = new numerical_constant_t NUM_TOP
                         
let bottomNumericalConstant = new numerical_constant_t NUM_BOTTOM
                            
let mkSymbolicConstant s = new symbolic_constant_t (SYM_CST s)
                         
let topSymbolicConstant = new symbolic_constant_t SYM_TOP
                        
let bottomSymbolicConstant = new symbolic_constant_t SYM_BOTTOM
                           
let mkBooleanConstant b = new boolean_constant_t (BOOL_CST b)
                        
let trueBooleanConstant = mkBooleanConstant true
let falseBooleanConstant = mkBooleanConstant false
                         
let topBooleanConstant = new boolean_constant_t BOOL_TOP

let bottomBooleanConstant = new boolean_constant_t BOOL_BOTTOM


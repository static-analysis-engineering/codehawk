(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
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
open CHLanguage   
open CHNumerical   
open CHPretty


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


type ordered_sym_cst_t =
  | ORDERED_SYM_BOTTOM
  | ORDERED_SYM_CST of symbol_t
  | ORDERED_SYM_TOP


(* s1 is less than s2 if the name of s2 is a substring of the name of s1
   (e.g., "aabb <= aab", but not "aaab <= aab").*)
let ordered_sym_leq (s1: symbol_t) (s2: symbol_t): bool =
  let n1 = s1#getBaseName in
  let n2 = s2#getBaseName in
  if n1 = n2 then
    true
  else
    let l1 = String.length n1 in
    let l2 = String.length n2 in
    if l1 <= l2 then
      false
    else
      (String.sub n1 0 l2) = n2


(* returns a string that is the common prefix of the name of s1 and the name
   of s2.*)
let sym_common_prefix (s1: symbol_t) (s2: symbol_t): string option =
  let n1 = s1#getBaseName in
  let n2 = s2#getBaseName in
  if n1 = n2 then
    Some n1
  else if n1 = "" || n2 = "" then
    None
  else
    let l1 = String.length n1 in
    let l2 = String.length n2 in
    let lmin = Stdlib.min l1 l2 in
    let s1sub = String.sub n1 0 lmin in
    let s2sub = String.sub n2 0 lmin in
    if s1sub = s2sub then
      Some n1
    else
      let rec common_prefix (l: int) =
        if l = 0 then
          None
        else
          let ss1 = String.sub n1 0 l in
          let ss2 = String.sub n2 0 l in
          if ss1 = ss2 then
            Some ss1
          else common_prefix (l - 1) in
      common_prefix (lmin - 1)


let ordered_sym_join (s1: symbol_t) (s2: symbol_t): symbol_t option =
  match sym_common_prefix s1 s2 with
  | Some name -> Some (new symbol_t name)
  | _ -> None


class ordered_symbolic_constant_t (s: ordered_sym_cst_t) =
object (self: 'a)

  val cst = s

  method getCst = cst

  method private mkNew s =
    {< cst = s >}

  method mkTop = {< cst = ORDERED_SYM_TOP >}

  method mkBottom = {< cst = ORDERED_SYM_BOTTOM >}

  method isTop =
    match cst with
    | ORDERED_SYM_TOP -> true
    | _ -> false

  method isBottom =
    match cst with
    | ORDERED_SYM_BOTTOM -> true
    | _ -> false

  method equal (c: 'a) =
    match (cst, c#getCst) with
    | (ORDERED_SYM_BOTTOM, ORDERED_SYM_BOTTOM) -> true
    | (ORDERED_SYM_TOP, ORDERED_SYM_TOP) -> true
    | (ORDERED_SYM_CST s1, ORDERED_SYM_CST s2) -> s1#equal s2
    | (_, _) -> false

  method leq (c: 'a) =
    match (cst, c#getCst) with
    | (ORDERED_SYM_BOTTOM, _) -> true
    | (_, ORDERED_SYM_TOP) -> true
    | (ORDERED_SYM_CST s1, ORDERED_SYM_CST s2) -> ordered_sym_leq s1 s2
    | (_, _) -> false

  method join (c: 'a) =
    match (cst, c#getCst) with
    | (ORDERED_SYM_TOP, _) -> {< >}
    | (_, ORDERED_SYM_TOP) -> c
    | (ORDERED_SYM_BOTTOM, _) -> c
    | (_, ORDERED_SYM_BOTTOM) -> {< >}
    | (ORDERED_SYM_CST s1, ORDERED_SYM_CST s2) ->
       if ordered_sym_leq s1 s2 then
         c
       else if ordered_sym_leq s2 s1 then
         {< >}
       else
         match ordered_sym_join s1 s2 with
         | None -> self#mkNew ORDERED_SYM_TOP
         | Some sym -> self#mkNew (ORDERED_SYM_CST sym)

  method meet (c: 'a) =
    match (cst, c#getCst) with
    | (ORDERED_SYM_TOP, _) -> c
    | (_, ORDERED_SYM_TOP) -> {< >}
    | (ORDERED_SYM_BOTTOM, _) -> {< >}
    | (_, ORDERED_SYM_BOTTOM) -> c
    | (ORDERED_SYM_CST s1, ORDERED_SYM_CST s2) ->
       if s1#equal s2 then
	 c
       else
	 self#mkNew ORDERED_SYM_BOTTOM

  method widening = self#join

  method narrowing = self#meet

  method toPretty =
    match cst with
    | ORDERED_SYM_BOTTOM -> STR "_|_"
    | ORDERED_SYM_TOP -> STR "T"
    | ORDERED_SYM_CST s -> s#toPretty

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

let mkOrderedSymbolicConstant (s: symbol_t) =
  new ordered_symbolic_constant_t (ORDERED_SYM_CST s)

let topOrderedSymbolicConstant =
  new ordered_symbolic_constant_t ORDERED_SYM_TOP

let bottomOrderedSymbolicConstant =
  new ordered_symbolic_constant_t ORDERED_SYM_BOTTOM

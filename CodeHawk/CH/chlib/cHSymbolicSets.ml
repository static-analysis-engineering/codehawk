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
open CHPretty
open CHUtils


type sym_set_t =
  | SET of SymbolCollections.set_t
  | TOP
  | BOTTOM
  
class symbolic_set_t (l: symbol_t list) =
object (self: 'a)
     
  val symbols = match l with
    | [] -> TOP
    | _ -> 
       let s = new SymbolCollections.set_t in
       let _ = s#addList l in
       SET s
       
  method getSymbols = symbols
                    
  method mkBottom = {< symbols = BOTTOM >}
                  
  method mkTop = {< symbols = TOP >}
               
  method isBottom = match symbols with
    | BOTTOM -> true
    | _ -> false
         
  method isTop = match symbols with
    | TOP -> true
    | _ -> false 
	 
  method equal (s: 'a) =
    match (symbols, s#getSymbols) with
    | (BOTTOM, BOTTOM) -> true
    | (TOP, TOP) -> true
    | (SET s1, SET s2) -> s1#equal s2
    | _ -> false
         
  method leq (s: 'a) =
    match (symbols, s#getSymbols) with
    | (BOTTOM, _) -> true
    | (_, TOP) -> true
    | (SET s1, SET s2) -> s1#subset s2
    | _ -> false
	 
  method delta (s: symbol_t list) =
    match symbols with
    | BOTTOM -> {< symbols = BOTTOM >}
    | TOP -> {< >}
    | SET s1 ->
       let s1' = s1#clone in
       let _ = List.iter (fun sym -> s1'#remove sym) s in
       if s1'#size = 0 then
	 {< symbols = BOTTOM >}
       else
	 {< symbols = SET s1' >}
       
  method join (s: 'a) =
    match (symbols, s#getSymbols) with
    | (BOTTOM, _) -> s
    | (_, BOTTOM) -> {< >}
    | (TOP, _) -> {< >}
    | (_, TOP) -> s
    | (SET s1, SET s2) ->
       {< symbols = SET (s1#union s2) >}
      
  method meet (s: 'a) =
    match (symbols, s#getSymbols) with
    | (BOTTOM, _) -> {< symbols = BOTTOM >}
    | (_, BOTTOM) -> {< symbols = BOTTOM >}
    | (TOP, _) -> s
    | (_, TOP) -> {< >}
    | (SET s1, SET s2) ->
       let result = s1#inter s2 in
       if result#size = 0 then
	 {< symbols = BOTTOM >}
       else
	 {< symbols = SET result >}
       
  method widening = self#join
                  
  method narrowing = self#meet
                   
  method contains s =
    match symbols with
    | TOP -> true
    | BOTTOM -> false
    | SET set -> set#has s
               
  method singleton =
    match symbols with
    | TOP -> None
    | BOTTOM -> None
    | SET set -> set#singleton
               
  method toPretty =
    match symbols with
    | BOTTOM -> STR "_|_"
    | TOP -> STR "{...}"
    | SET s -> s#toPretty
             
  method iter f =
    match symbols with
    | SET s -> s#iter f
    | _ -> raise (CHFailure (STR "Iteration over an unbounded symbolic set"))
	 
end

let topSymbolicSet = new symbolic_set_t []
                   
let bottomSymbolicSet = topSymbolicSet#mkBottom
                      
                      

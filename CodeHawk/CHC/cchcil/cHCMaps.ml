(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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

open CHPrettyPrint

exception Duplicate_found of string

module type STRINGMAP =
sig

  type +'a t

  val empty: 'a t
  val is_empty: 'a t -> bool
  val get: string -> 'a t -> 'a option
  val add: string -> 'a -> 'a t -> 'a t
  val keys: 'a t -> string list
  val fold: (string -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val addUnique: string -> 'a -> 'a t -> 'a t
  val addUniquePairs: (string * 'a) list -> 'a t -> 'a t
  val listOfPairs: 'a t -> (string * 'a) list
  val toPretty: 'a t -> ('a -> pretty_t) -> pretty_t

end


module StringMap:STRINGMAP =
struct

  module PreStringMap =
    Map.Make (struct
	       type t = string
	       let compare = Stdlib.compare
	     end)

  include PreStringMap

  let get (k:string) (m:'a t):'a option =
    try Some (find k m) with Not_found -> None

  let keys (m:'a t):string list = fold (fun k _ a -> k::a) m []

  let addUnique (k:string) (v:'a) (m:'a t):'a t = 
    match get k m with 
    |	Some _ -> raise (Duplicate_found k)
    | _ -> add k v m
         
  let addUniquePairs (pairs:((string * 'a) list)) (m:'a t):'a t = 
    List.fold_right (fun (k,v) a -> addUnique k v a) pairs m
    
  let listOfPairs (m:'a t):(string * 'a) list =
    fold (fun k v a -> (k,v) :: a) m []
                                              
  let toPretty (m:'a t) (p:'a -> pretty_t):pretty_t =
    fold (fun k v a ->
        LBLOCK [a; NL; STR k; STR  " -> "; p v]) m (LBLOCK [])

end

module type INTMAP =
sig
  type +'a t

    val mapMerge: 'a t -> 'a t -> ('a -> 'a -> 'a) -> 'a t
    val get: int -> 'a t -> 'a option
    val add: int -> 'a -> 'a t -> 'a t
    val empty: 'a t
end

module IntMap:INTMAP =
struct
  
  module PreIntMap =
    Map.Make (struct
	       type t = int
	       let compare = Stdlib.compare
	     end)
    
  include PreIntMap
				 
  let mapMerge (m1:'a t) (m2:'a t) (f: 'a -> 'a -> 'a):'a t =
    fold (fun k v a ->
            let b = mem k a in
              if b then
                let n = f v (find k a) in
                  add k n a
              else
                add k v a) m1 m2
      
  let get (k:int) (m:'a t):'a option =
    try Some (find k m) with Not_found -> None
    
  let toPretty (m:'a t) (p:'a -> pretty_t):pretty_t =
    let elts = fold (fun k v a -> LBLOCK [INT k; STR " -> "; p v; NL; a]) 
      m (LBLOCK []) in
      LBLOCK [STR "{"; NL; INDENT (2, elts); STR "}"]
	
end



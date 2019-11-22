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
open CHPretty

exception Not_included

module Make (S: STOREABLE) =
struct

  module ObjectMap = Map.Make (S)
      
  module ObjectSet = Set.Make (S)
      
  class set_t =
  object (self: 'a)
    
    val mutable objectSet = ObjectSet.empty
      
    val mutable count = 0

    method size = count
      
    method clone = {< >}

    method private mkNew = {< count = 0; objectSet = ObjectSet.empty >}

    method has x = ObjectSet.mem x objectSet
      
    method isEmpty = (count = 0)

    method subset (s: 'a) =
      if s#size < self#size then
	false
      else
	try
	  let _ = ObjectSet.iter (fun x -> if s#has x then () else raise Not_included) objectSet in
	    true
	with Not_included -> false
	  
    method equal (s: 'a) =
      if s#size = self#size then
	self#subset s
      else
	false

    method add x =
      if ObjectSet.mem x objectSet then
	()
      else
	begin
	  objectSet <- ObjectSet.add x objectSet;
	  count <- count + 1
	end

    method choose =
      try
	Some (ObjectSet.choose objectSet)
      with
	  Not_found -> None
	  
    method addList elts =
      let rec loop l =
	match l with
	  | [] -> ()
	  | x :: l ->
	      begin
		self#add x;
		loop l
	      end
      in
	loop elts

    method addSet (s: 'a) =
      s#iter (fun e -> self#add e)

    method remove x =
      if ObjectSet.mem x objectSet then
	begin
	  objectSet <- ObjectSet.remove x objectSet;
	  count <- count - 1
	end
      else
	()

    method removeList l =
      List.iter (fun x -> self#remove x) l
	  
    method iter f =
      ObjectSet.iter f objectSet

    method fold: 'a. ('a -> S.t -> 'a) -> 'a -> 'a =
      fun f acc -> ObjectSet.fold (fun e a -> f a e) objectSet acc

    method union (a: 'a) =
      if a#size < count then
	a#union self
      else
	let res = a#clone in
	let _ = ObjectSet.iter (fun x -> res#add x) objectSet in
	  res
	  
    method inter (a: 'a) =
      if a#size < count then
	a#inter self
      else
	let res = self#mkNew in
	let _ = ObjectSet.iter (fun x -> if a#has x then res#add x else ()) objectSet in
	  res

    method diff (a: 'a) =
      let res = self#mkNew in
      let _ = ObjectSet.iter (fun x -> if a#has x then () else res#add x) objectSet in
	res

    method filter f =
      let res = self#mkNew in
      let _ = ObjectSet.iter (fun x -> res#add x) (ObjectSet.filter f objectSet) in
	res

    method toList =
      ObjectSet.elements objectSet
	  
    method toPretty =
      pretty_print_list self#toList S.toPretty "{" "; " "}" 

    method singleton =
      if count = 1 then
	Some (ObjectSet.choose objectSet)
      else
	None
	  
  end
  
  class ['v] simple_table_t =
  object (self: 'a)
    
    val mutable table = ObjectMap.empty
      
    val mutable count = 0
      
    method size = count
      
    method clone = {< >}
	  
    method private mkNew = {< count = 0; table = ObjectMap.empty >}
      
    method has x = ObjectMap.mem x table

    method get x =
      try
	Some (ObjectMap.find x table)
      with Not_found -> None
	
    method set x (v: 'v) =
      let _ = if ObjectMap.mem x table then
	()
      else
	count <- count + 1
      in
	table <- ObjectMap.add x v table;
	
    method remove x =
      if ObjectMap.mem x table then
	begin
	  table <- ObjectMap.remove x table;
	  count <- count - 1
	end
      else
	()
	  
    method removeList l =
      List.iter (fun x -> self#remove x) l	  

    method iter f =
      ObjectMap.iter f table

    method fold: 'a. ('a -> S.t -> 'v -> 'a) -> 'a -> 'a =
      fun f acc -> ObjectMap.fold (fun e v a -> f a e v) table acc

    method map f =
      {< table = ObjectMap.map f table >}

    method mapi f =
      {< table = ObjectMap.mapi f table >}

    method keys =
      let k = new set_t in
      let _ = ObjectMap.iter (fun key _ -> k#add key) table in
	k

    method listOfKeys =
      ObjectMap.fold (fun k _ l -> k :: l) table []

    method setOfKeys =
      let s = new set_t in
      let _ = s#addList self#listOfKeys in
	s

    method listOfValues =
      ObjectMap.fold (fun _ v l -> v :: l) table []

    method listOfPairs =
      ObjectMap.fold (fun k v l -> (k, v) :: l) table []
	  
  end

  class ['v] table_t =
  object
    
    inherit ['v] simple_table_t

    method toPretty =
      let elts = ObjectMap.fold (fun k v a ->
                     LBLOCK [(S.toPretty k); STR " -> "; v#toPretty; NL; a]) table (LBLOCK []) in
      LBLOCK [STR "{"; NL;
	      INDENT (2, elts);
	      STR "}"]

  end

  let set_of_list l =
    let s = new set_t in
    let _= s#addList l in
    s
    
end

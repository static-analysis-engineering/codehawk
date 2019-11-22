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

module Make (E: STOREABLE) =
struct
  
  module C = CHCollections.Make (E)
    
  class uf_node_t (e: E.t) (table: uf_node_table_t) =
  object (self: 'a)
    
    val mutable parent = e

    val mutable rank = 0

    method parent = parent

    method rank = rank

    method setParent e' = parent <- e'

    method incRank = rank <- rank + 1

    method element = e

    method link (x: 'a) =
      if rank > x#rank then
	x#setParent e
      else
	begin
	  parent <- x#element;
	  if rank = x#rank then
	    x#incRank
	  else
	    ()
	end

    method findSet =
      let node = match table#get parent with
	| None -> raise (CHFailure (LBLOCK [STR "Union Find: Set of element ";
                                            E.toPretty parent; STR " not found"]))
	| Some n -> n
      in
      if e == parent then
	node
      else
	node#findSet
      
    method union (x: 'a) =
      self#findSet#link x#findSet
      
  end

    and uf_node_table_t = [uf_node_t] C.simple_table_t
      
  class union_find_t =
  object (self: _)
    
    val mutable uf_node_table: uf_node_table_t = new uf_node_table_t
      
    method private getSet (x: E.t) =
      match uf_node_table#get x with
	| Some n -> n
	| None -> 
	  let n = new uf_node_t x uf_node_table in
	  let _ = uf_node_table#set x n in
	  n

    method union (x: E.t) (y: E.t) =
      let n_x = self#getSet x in
      let n_y = self#getSet y in
      n_x#union n_y
      
    method find (x: E.t) =
      (self#getSet x)#findSet#element
	
    method reset = uf_node_table <- new uf_node_table_t

  end
    
  class virtual ['a] union_find_with_attributes_t =
  object (self: _)
    
    inherit union_find_t as super
      
    val mutable attribute_table: 'a C.simple_table_t = new C.simple_table_t

    method virtual mergeAttributes: 'a -> 'a -> 'a
      
    method set (x: E.t) (a: 'a) =
      let e = self#find x in
      let e_att = match attribute_table#get e with
	| None -> a
	| Some a' -> self#mergeAttributes a a'
      in
      attribute_table#set e e_att
	
    method get (x: E.t) = attribute_table#get (self#find x)

    method union (x: E.t) (y: E.t) =
      let e_x = self#find x in
      let e_y = self#find y in
      let att = match (attribute_table#get e_x, attribute_table#get e_y) with
	| (None, None) -> None
	| (Some a, None) -> Some a
	| (None, Some a') -> Some a'
	| (Some a, Some a') -> Some (self#mergeAttributes a a')
      in
      begin
	super#union x y;
	attribute_table#remove e_x;
	attribute_table#remove e_y;
	match att with
	  | None -> ()
	  | Some a -> attribute_table#set (self#find x) a
      end
	
    method reset =
      super#reset;
      attribute_table <- new C.simple_table_t
	
  end

end
  

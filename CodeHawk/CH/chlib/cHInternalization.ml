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

module Make (OBJECT: HASH_STOREABLE) =
struct
  
  class internal_table_t ?(store_ids = true) (s: int) =
    let good_prime_sizes = [
      97;
      193;
      389;
      769;
      1543;
      3079;
      6151;
      12289;
      24593;
      49157;
      98317;
      196613;
      393241;
      786433;
      1572869;
      3145739;
      6291469;
      12582917;
      25165843;
      50331653;
      100663319;
      201326611;
      402653189;
      805306457
    ]
    in
    let find_nearest_prime_size s =
      let rec scan l =
	match l with
	| [] -> raise (CHFailure (LBLOCK [STR "Internalization: requested table size ";
                                          INT s; STR " is too large"]))
	| p :: l' -> if s <= p then p else scan l'
      in
      scan good_prime_sizes
    in
    let p = find_nearest_prime_size s in
    object (self: _)
    
      val mutable size = p

      val mutable object_count = 0
                               
      val mutable object_table: OBJECT.t option array = Array.make p None
                                                      
      val mutable id_table: int array = if store_ids then Array.make p 0 else Array.make 0 0

      method private hash (x: OBJECT.t) =
        let h = OBJECT.hash x in
        (h mod size, 1 + (h mod (size - 1)))
	
      method private probe (x: OBJECT.t) =
        let (h, h') = self#hash x in
        let rec scan s =
	  match object_table.(s) with
	  | None -> s
	  | Some x' ->
	     if OBJECT.compare x x' = 0 then
	       s
	     else
	       scan ((s + h') mod size)
        in
        scan h
	
      method private resize =
        let old_size = size in
        let p' = find_nearest_prime_size (size + 1) in
        size <- p';
        let old_object_table = object_table in
        let old_id_table = id_table in
        object_table <- Array.make p' None;
        if store_ids then id_table <- Array.make p' 0 else ();
        for s = 0 to old_size - 1 do
	  match old_object_table.(s) with
	  | None -> ()
	  | Some x ->
	     let s' = self#probe x in
	     object_table.(s') <- Some x;
	     if store_ids then 
	       let id = old_id_table.(s) in
	       id_table.(s') <- id
	     else
	       ()
        done
	
      method internalize (x: OBJECT.t) =
        if object_count = size then 
	  self#resize 
        else 
	  ();
        let s = self#probe x in
        match object_table.(s) with
	| None ->
	   let id = object_count + 1 in
	   let _ = object_count <- id in
	   let _ = object_table.(s) <- Some x in
	   let _ = if store_ids then id_table.(s) <- id else () in
	   (id, x)
	| Some x' ->
	   ((if store_ids then id_table.(s) else 0), x')
	  
    end
    
end

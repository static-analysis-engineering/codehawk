(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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


let rec string_replace (c:char) (r:string) (s:string):string =
  try
    let i = String.index s c in
    let prefix = String.sub s 0 i in
    let suffix = string_replace c r (String.sub s (i+1) ((String.length s) - i -1)) in
    prefix ^ r ^ suffix
  with Not_found -> s

let string_nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  begin
    while !start < len do
      let s_index = try String.index_from s !start separator with Not_found -> len in
      let substring = String.sub s !start (s_index - !start) in
      begin
	result := substring :: !result ;
	start := s_index + 1
      end 
    done;
    !result
  end
  

(* Split a list into two lists, the first one with n elements,
   the second list with the remaining (if any) elements
*)
let list_split (n:int) (l:'a list):('a list * 'a list) =
  let rec loop i p l =
    if i = n then 
      (List.rev p,l)
    else loop (i+1) ((List.hd l)::p) (List.tl l) in
  if (List.length l) <= n then (l,[]) else loop 0 [] l

(* Split a list into two lists, the first with the elements
   from l on which predicate p is true, the second one on
   which p is false
*)
let list_split_p (p:'a -> bool) (l:'a list):('a list * 'a list) =
  let rec loop ptrue pfalse l =
    match l with
    | [] -> (List.rev ptrue, List.rev pfalse)
    | h::tl -> if p h then loop (h::ptrue) pfalse tl else loop ptrue (h::pfalse) tl in
  loop [] [] l

let list_suffix (n:int) (l:'a list) =
  let rec aux n l =
    match l with 
    | [] -> []
    | _ -> if n=0 then l else aux (n-1) (List.tl l) in
  if n >= 0 then 
    aux n l
  else
    raise (Invalid_argument "cannot take a negative suffix of a list")


(* Remove duplicates from l with standard equality check; order is preserved *)
let remove_duplicates (l:'a list):'a list =
  let rec aux l r =
    match l with
    | [] -> r
    | h::tl -> if List.mem h r then (aux tl r) else (aux tl (h::r)) in
  List.rev (aux l [])

(* Remove duplicates from l using f as an equality check; order is preserved *)
let remove_duplicates_f (l:'a list) (f:'a -> 'a -> bool):'a list =
  let rec aux l r =
    match l with
    | [] -> r
    | h::tl -> if List.exists (fun e -> f e h) r then (aux tl r) else (aux tl (h::r)) in
  List.rev (aux l [])

(* Return the union of two lists, using f as an equality check *)
let list_union_f (l1:'a list) (l2:'a list) (f:'a -> 'a -> bool):'a list = 
    remove_duplicates_f (l1 @ l2) f

(* Return the difference of two lists, using f as an equality check *)
let list_difference (l:'a list) (s:'a list) (f:'a -> 'a -> bool):'a list =
    let rec aux l r =
      match l with
      | [] -> r
      | h::tl -> if List.exists (fun e -> f h e) s then (aux tl r) else (aux tl (h::r)) in
    aux l []

(* Return the maximum element from a list, using f as comparison function *)
let list_maxf (l:'a list) (f:'a -> 'a -> int):'a =  
    match l with
    | [] -> failwith "List.maxf : empty list"
    | _ ->
	List.fold_right (fun e m -> if f e m = 1 then e else m) l (List.hd l)

(* Compares two lists of equal length element by element, using f as comparison function *)
let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
    if (List.length l1) = (List.length l2) then
      let c = List.fold_left2 (fun a e1 e2 -> if a = 0 then (f e1 e2) else a) 0 l1 l2 in
      Pervasives.compare c 0
    else
      failwith "List.lcompare : not applicable to lists of unequal length"

(* create the cross product of two lists *)
let xproduct (l1:'a list) (l2:'a list):('a * 'a) list =
  List.concat (List.map (fun x -> List.map (fun y -> (x,y)) l2) l1)

let list_sub (l:'a list) (s:int) (n:int):'a list =
  let len = List.length l in
  if s < 0 then
    raise (Invalid_argument "list_sub: negative start index")
  else if s + n > len then
    raise (Invalid_argument
             ("list_sub: length out of bounds; "
              ^ " s: " ^ (string_of_int s)
              ^ "; n: " ^ (string_of_int n)
              ^ "; len: " ^ (string_of_int  len)))
  else if n < 0 then
    raise (Invalid_argument "list_sub: negative length")
  else
    let rec suffix l n =
      match l with
      | [] -> []
      | _ -> if n = 0 then l else suffix (List.tl l) (n-1)  in
    let l' = suffix l s in
    let rec sub l n result =
      if n = 0 then result else sub (List.tl l) (n-1) ((List.hd l)::result)  in
    List.rev (sub l' n [])

(* Fold left on an array with access to the array index *)
let array_fold_lefti (f: 'b -> int -> 'a -> 'b) (init: 'b) (a: 'a array) =
  let (_,r) = Array.fold_left 
      (fun (i,acc) v -> let r = f acc i v in (i+1,r)) (0,init) a in
  r

(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
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
   ============================================================================= *)

(** Translated unstructured statements to CHIF *)

(* chlib *)
open CHPretty

(* cchlib *)
open CCHBasicTypes

(* cchanalyze *)
open CCHAnalysisTypes


let get_gotos (b:block) =
  let rec aux stmt gotos =
    match stmt.skind with
    | Goto (i,_) ->  (stmt.sid,i) :: gotos
    | If (_, b1, b2, _) ->
       let g = aux_list b1.bstmts gotos in  aux_list b2.bstmts g
    | Loop (b,_,_,_)
    | Switch (_, b, _, _)
    | Block b -> aux_list b.bstmts gotos
    | _ -> gotos
  and aux_list lst gotos =
    List.fold_right (fun s a -> aux s a) lst gotos in
  aux_list b.bstmts []
    
let get_ancestors (id:int) (b:block) =
  let rec aux id stmt ancs =
    if stmt.sid = id then
      Some ancs
    else
      match stmt.skind with
      | If (_, b1, b2, _) ->
	begin
	  match aux_list id b1.bstmts ancs with
	  | Some v ->	Some (stmt.sid :: v)
	  | _ ->
	    match aux_list id b2.bstmts ancs with
	    | Some v ->	Some (stmt.sid ::v)
	    | _ -> None
	end
      | Loop (b, _, _, _)
      | Switch (_, b, _, _)
      | Block b ->
	begin
	  match aux_list id b.bstmts ancs with
	  | Some v ->	Some (stmt.sid :: v)
	  | _ -> None
	end
      | _ -> None
  and aux_list id lst ancs =
    match lst with
    | [] -> None
    | h :: tl ->
      match aux id h ancs with
      | Some v ->	Some v
      | _ -> aux_list id tl ancs
  in
  aux_list id b.bstmts []
    
let get_descendants stmt =
  let rec aux s =
    let id = s.sid in
    match s.skind with
    | If (_, b1, b2, _) ->
      let b1_desc = aux_list b1.bstmts in
      let b2_desc = aux_list b2.bstmts in
      id :: (b1_desc @ b2_desc)
    | Loop (b, _, _, _)
    | Switch (_, b, _, _)
    | Block b -> id :: (aux_list b.bstmts)
    | _ -> [ id ]
  and aux_list lst =
    List.fold_right (fun s a -> (aux s) @ a) lst [] in
  aux stmt
    
    
class gotos_t (b:block):gotos_int =
object 
  
  val cfg_ids:(int option list) = 
    let goto_pairs = get_gotos b in
    let ids = ref [] in
    let add_least_common_ancestor (b:block) (src,tgt) =
      let get_list l = match l with Some v -> v | _ -> [] in
      let src_ancestors = get_list (get_ancestors src b) in
      let tgt_ancestors = get_list (get_ancestors tgt b) in
      let rec match_src_tgt s t id =
	match (s,t) with
	  ([],_)
	| (_,[]) -> ids := id :: !ids
	| (src_hd :: src_tl, tgt_hd :: tgt_tl) when src_hd = tgt_hd ->
	  match_src_tgt src_tl tgt_tl (Some src_hd)
	| _ -> ids := id :: !ids
      in
      match_src_tgt src_ancestors tgt_ancestors None in				
    begin
      List.iter (fun g -> add_least_common_ancestor b g) goto_pairs ;
      !ids
    end		
      
  method is_goto_function =
    List.exists (fun s -> match s with None -> true | _ -> false) cfg_ids
      
  method is_goto_block stmt =
    List.exists (fun s -> match s with Some v -> v = stmt.sid | _ -> false) cfg_ids
      
      
end

let make_gotos = new gotos_t 
  

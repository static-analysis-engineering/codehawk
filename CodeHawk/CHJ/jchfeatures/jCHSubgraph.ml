(* =============================================================================
   CodeHawk Java Analyzer
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

(* chlib *)
open CHLanguage
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHIFSystem
open JCHPreAPI
open JCHSystemSettings

module H = Hashtbl
module P = Pervasives

let maxlen = 750

let cfg_skeleton_to_pretty (table:(string,int) H.t) (cfg:cfg_int) =
  let states = List.rev (cfg#getStatesFrom cfg#getEntry#getLabel) in
  LBLOCK ( List.map (fun s ->
    let state = cfg#getState s in
    LBLOCK [ INT (H.find table s#getBaseName) ; STR "  " ; s#toPretty ; STR ": " ; 
	     pretty_print_list state#getOutgoingEdges (fun s -> s#toPretty) "[" ", " "]" ;
	       NL ]) states)

let table_to_pretty (table:(int,int list) H.t) =
  let l = ref [] in
  let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
  let l = List.sort (fun (i1,_) (i2,_) -> P.compare i1 i2) !l in
  LBLOCK (List.map (fun (k,v) -> 
    LBLOCK [ INT k ; STR ": " ; 
	     pretty_print_list v (fun i -> INT i) "{" "," "}" ; NL ]) l)

let get_subsets (n:int) (l:'a list) =
  let rec aux n l =
    if n = 0 then 
      [ [] ]
    else
      match l with
      | [] -> []
      | h::tl ->
	let len = List.length l in
	if len < n then []
	else if len = n then [ l ]
	else
	  (List.map (fun s -> h :: s) (aux (n-1) tl)) @ (aux n tl) in
  aux n l
	  
let get_edges (cfg:cfg_int) =
  let states = cfg#getStatesFrom (cfg#getEntry#getLabel) in
  List.concat (List.map (fun s ->
    let state = cfg#getState s in
    List.map (fun t -> (s,t)) state#getOutgoingEdges) states)

let matrix_to_pretty (m:int array array) =
  let p = ref [] in
  let _ = for i = 0 to 3 do 
      begin
	for j = 0 to 3 do
	  p := (LBLOCK [ INT m.(i).(j) ; STR "  " ]) :: !p
	done ;
	p := NL :: !p
      end
    done in
  LBLOCK [ LBLOCK (List.rev !p) ; NL ] 

let varray = Array.make 4 0
let _ = varray.(3) <- 1 
let _ = varray.(2) <- 2 
let _ = varray.(1) <- 4 
let _ = varray.(0) <- 8

let encode_matrix (m:int array array) =
  let encode_row (r:int array) =
    let v = ref 0 in
    begin for i = 0 to 3 do v := !v + (varray.(i) * r.(i)) done ; !v end in
  let to_hex v = if v < 10 then string_of_int v else
      match v with
      | 10 -> "a"
      | 11 -> "b"
      | 12 -> "c"
      | 13 -> "d"
      | 14 -> "e"
      | 15 -> "f"
      | _ -> raise (JCH_failure (LBLOCK [ STR "Unexpected number: " ; INT v ])) in
  String.concat "" (List.map (fun i -> to_hex (encode_row m.(i))) [ 0 ; 1 ; 2 ; 3 ])

let range (n:int):int list = ExtList.List.init n (fun i -> i)

let is_reachable (succs:(int,int list) H.t) (start:int) (l:int list) =
  if List.mem start l then
    let getSuccs i =
      if H.mem succs i then List.filter (fun k -> List.mem k l) (H.find succs i) else
	raise (JCH_failure (STR "Internal error in is_reachable")) in
    let nodeSet = new IntCollections.set_t in
    let _ = nodeSet#add start in
    let added = ref true in
    let _ = while !added do
	let size = nodeSet#size in
	begin
	  nodeSet#addList (List.concat (List.map getSuccs nodeSet#toList)) ;
	  added := nodeSet#size > size
	end 
      done in
    nodeSet#size = (List.length l)
  else
    false

let make_adj_matrix (succs:(int,int list) H.t) (l:int list) =
  let t = H.create 4 in
  let _ = List.iteri (fun i n -> H.add t n i) (List.sort P.compare l) in
  let getI i = if H.mem t i then H.find t i else 
      raise (JCH_failure (STR "Internal error in make_adj_matrix 1")) in
  let getSuccs i = if H.mem succs i then 
      List.filter (fun k -> List.mem k l) (H.find succs i) 
    else
      raise (JCH_failure (STR "Internal error in make_adj_matrix 2")) in
  let m = Array.make_matrix 4 4 0 in
  let _ = List.iter (fun i -> 
    List.iter (fun succ -> m.(getI i).(getI succ) <- 1) (getSuccs i)) l in
  m

let encode (succs:(int,int list) H.t) (start:int):string list =
  let nodeSet = new IntCollections.set_t in
  let _ = nodeSet#add start in
  let _ = for i = 1 to 3 do 
      nodeSet#addList (List.concat (List.map (H.find succs) (nodeSet#toList))) done in
  if nodeSet#size > 100 then
    let _ = system_settings#log_error 
      (LBLOCK [ STR "Skip subgraphs for starting node: " ; INT start ; 
		STR " with reachable set of size " ; INT nodeSet#size ]) in
    [ "skip" ]
  else
    let sub4Sets = List.filter (is_reachable succs start) (get_subsets 4 nodeSet#toList) in
    List.map encode_matrix (List.map (make_adj_matrix succs) sub4Sets)
    
let get_cfg_4subgraphs (proc:procedure_int) = 
  let rec get_cfg code =
    match code#getCmdAt 0 with
    | RELATION cd -> get_cfg cd
    | CFG (_, cfg) -> cfg
    | cmd -> raise (JCH_failure (STR "get_cfg: expexted CODE [ CFG cfg ; ... ] ")) in
  let cfg = get_cfg proc#getBody in
  let states = List.rev (cfg#getStatesFrom cfg#getEntry#getLabel) in
  let edges = get_edges cfg in
  let nameTable = H.create (List.length states) in
  let _ = List.iteri (fun i s -> H.add nameTable s#getBaseName i) states in
  let getI s = if H.mem nameTable s#getBaseName then H.find nameTable s#getBaseName else
      raise (JCH_failure (STR "Internal error in cfg_4subgraphs")) in
  let succTable = H.create (List.length states) in
  let _ = List.iter (fun s ->
    let succs = (cfg#getState s)#getOutgoingEdges in
    H.add succTable (getI s) (List.map getI succs)) states in
  (List.concat (List.map (encode succTable) (range (List.length states))), List.length states,
  List.length edges)


let print_encodings (mInfo:method_info_int) =
  let proc = get_chif mInfo#get_class_method_signature in
  let (encodings,nStates,nEdges) = get_cfg_4subgraphs proc in
  pr_debug [ mInfo#get_class_method_signature#toPretty ; NL ;
	     STR "  States: " ; INT nStates ; STR ";  Edges: " ; INT nEdges ; NL ;
	     INDENT (2, LBLOCK (List.map (fun s -> LBLOCK [ STR s ; NL ]) encodings)) ; NL ]

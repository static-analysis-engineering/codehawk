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

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHFileEnvironment
open CCHTypesUtil
open CCHUtilities

(* cchpre *) 
open CCHPreTypes
open CCHProofObligation

module P = Pervasives

let data_structure_assumption_compare d1 d2 =
  match (d1,d2) with
  | (DNotNull s1, DNotNull s2) -> Pervasives.compare s1 s2
  | (DNotNull _, _) -> -1
  | (_, DNotNull _) -> 1
  | (DUpperBound s1, DUpperBound s2) -> Pervasives.compare s1 s2
  | (DUpperBound _, _) -> -1
  | (_, DUpperBound _) -> 1
  | (DLowerBound s1, DLowerBound s2) -> Pervasives.compare s1 s2
  | (DLowerBound _, _) -> -1
  | (_, DLowerBound _) -> 1
  | (DValidMem s1, DValidMem s2) -> Pervasives.compare s1 s2
  | (DValidMem _, _) -> -1
  | (_, DValidMem _) -> 1
  | (DInitialized s1,DInitialized s2) -> Pervasives.compare s1 s2
  | (DInitialized _,_) -> -1
  | (_,DInitialized _) -> 1
  | (DEquals (s1,v1),DEquals (s2,v2)) ->
    let l0 = Pervasives.compare s1 s2 in if l0 = 0 then P.compare v1 v2 else l0


class data_structure_invariant_t
        (ckey:int) (name:string) (assumptions:data_structure_assumption_t list) =
object (self)

  method private has (d:data_structure_assumption_t) =
    List.exists (fun dd -> (data_structure_assumption_compare d dd) = 0) assumptions
      
  method has_assumption (env:file_environment_int) (p:po_predicate_t) =
    let get_lval_key lval = 
      match lval with
      | (Mem _,Field ((fname,fckey),NoOffset)) -> fckey
      | _ -> (-1) in
    let get_key e =	match e with Lval lval -> get_lval_key lval | _ -> (-1) in
    let get_lval_field lval =
      match lval with
      | (Mem _,Field ((fname,_),NoOffset)) -> fname
      | _ -> "" in
    let get_field e = match e with Lval lval -> get_lval_field lval | _ -> "" in
    let has = match p with
      | PNotNull e -> (get_key e) = ckey && self#has (DNotNull (get_field e))
      | PValidMem e -> (get_key e) = ckey && self#has (DValidMem (get_field e))
      | PInitialized lval ->
	(get_lval_key lval) = ckey && self#has (DInitialized (get_lval_field lval))
      | PLowerBound (_,e) -> 
	(get_key e) = ckey && self#has (DLowerBound (get_field e))
      | PUpperBound (_,e) -> 
	(get_key e) = ckey && self#has (DUpperBound (get_field e))
      | _ -> false in
    if has then Some name else None

end

class data_structure_invariants_t (l:data_structure_invariant_t list) =
object
  method has_assumption env (p:po_predicate_t) =
    List.fold_left (fun acc a -> match acc with 
    | Some _ -> acc | _ -> a#has_assumption env p) None l
end

let read_xml_data_structure_invariant (node:xml_element_int) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let gkey = geti "gkey" in
  let name = get "name" in
  let predicates = List.map (fun n ->
    let p = n#getAttribute "predicate" in
    let fname = n#getAttribute "fname" in
    match p with
    | "not-null" -> DNotNull fname
    | "valid-mem" -> DValidMem fname
    | "lower-bound" -> DLowerBound fname
    | "upper-bound" -> DUpperBound fname
    | "initialized" -> DInitialized fname
    | "equals" -> DEquals (fname,geti "value")
    | _ -> raise (CCHFailure 
		    (LBLOCK [ STR "Data structure predicate " ; STR p ; 
			      STR " not recognized" ]))) 
    (node#getTaggedChildren "assume") in
  new data_structure_invariant_t gkey name predicates

let read_xml_data_structure_invariants (node:xml_element_int) =
  let invariants = List.map read_xml_data_structure_invariant 
    (node#getTaggedChildren "data-structure-invariant") in
  new data_structure_invariants_t invariants


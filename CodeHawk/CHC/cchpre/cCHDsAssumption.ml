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
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHPODictionary
open CCHProofObligation
open CCHPreTypes


let pd = CCHPredicateDictionary.predicate_dictionary

let write_xml_dependent_proof_obligations (node:xml_element_int) (l:string list) =
  let l = List.sort Pervasives.compare l in
  node#appendChildren (List.map (fun i ->
    let iNode = xmlElement "po" in begin iNode#setAttribute "id" i ; iNode end) l) 

class ds_assumption_t ?(pos=[]) (index:int):ds_assumption_int =
object (self)

  val mutable dependent_ppos = List.filter (fun i -> i > 0) pos
  val mutable dependent_spos = List.filter (fun i -> i < 0) pos

  method add_dependents (pos:int list) =
    begin
      dependent_ppos <- (List.filter (fun i -> i > 0) pos) @ dependent_ppos ;
      dependent_spos <- (List.filter (fun i -> i < 0) pos) @ dependent_spos
    end

  method index = index

  method get_predicate = pd#get_po_predicate index

  method get_dependent_ppos = dependent_ppos

  method get_dependent_spos = dependent_spos

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    begin
      (if (List.length dependent_ppos) > 0 then
         set "ppos" (String.concat "," (List.map string_of_int dependent_ppos))) ;
      (if (List.length dependent_spos) > 0 then
         let spos = List.map (fun i -> (-i)) dependent_spos in
         set "spos" (String.concat "," (List.map string_of_int spos))) ;
      seti "ipr" index
    end

end

let mk_ds_assumption ?(pos=[]) (index:int):ds_assumption_int = 
  new ds_assumption_t ~pos index

let read_xml_ds_assumption (node:xml_element_int) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let index = geti "ipr" in
  let ppos = if has "ppos" then
               List.map int_of_string (nsplit ',' (get "ppos")) else [] in
  let spos = if has "spos" then
               List.map int_of_string (nsplit ',' (get "spos")) else [] in
  let spos = List.map (fun i -> (-i)) spos in
  mk_ds_assumption ~pos:(ppos@spos) index
    
    

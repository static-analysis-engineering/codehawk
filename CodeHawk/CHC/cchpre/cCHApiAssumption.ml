(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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
open CCHUtilities

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes

module H = Hashtbl


let pd = CCHPredicateDictionary.predicate_dictionary


class api_assumption_t
        ?(isfile=false)
        ?(ppos=[])
        ?(isglobal=false)
        ?(spos=[])
        (index:int):api_assumption_int =
object
  
  val mutable dependent_ppos = ppos
  val mutable dependent_spos = spos

  method add_dependent_ppo (ippo:int) =
    if List.mem ippo dependent_ppos then
      ()
    else
      dependent_ppos <- ippo :: dependent_ppos

  method add_dependent_spo (ispo:int) =
    if List.mem ispo dependent_spos then
      ()
    else
      dependent_spos <- ispo :: dependent_spos

  method index = index
    
  method get_predicate = pd#get_po_predicate index
    
  method get_dependent_ppos = dependent_ppos

  method get_dependent_spos = dependent_spos

  method toPretty = po_predicate_to_pretty (pd#get_po_predicate index)

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    begin
      (if (List.length dependent_ppos) > 0 then
         set "ppos" (String.concat "," (List.map string_of_int dependent_ppos)));
      (if (List.length dependent_spos) > 0 then
         set "spos" (String.concat "," (List.map string_of_int dependent_spos)));
      seti "ipr" index;
      (if isglobal then set "global" "yes");
      (if isfile then set "file" "yes")
    end
   
end


let mk_api_assumption
      ?(isfile=false)
      ?(isglobal=false)
      ?(ppos=[])
      ?(spos=[])
      (index:int):api_assumption_int =
  new api_assumption_t ~isfile ~isglobal ~ppos ~spos index


let read_xml_api_assumption (node:xml_element_int) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let index = geti "ipr" in
  try
    let ppos =
      if has "ppos" then
        List.map int_of_string (nsplit ',' (get "ppos")) else [] in
    let spos =
      if has "spos" then
        List.map int_of_string (nsplit ',' (get "spos")) else [] in
    let isglobal = has "global" &&  (get "global") = "yes"  in
    let isfile = has "file" && (get "file") = "yes" in
    mk_api_assumption ~isfile ~isglobal ~ppos ~spos index
  with
  | Failure _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "read_xml_api_assumption: int_of_string on ";
               STR (get "ppos");
               STR " and ";
               STR (get "spos")]))

    
    

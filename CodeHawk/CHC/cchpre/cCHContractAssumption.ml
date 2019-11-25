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
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHExternalPredicate
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHProofObligation
open CCHPreTypes


module H = Hashtbl

let id = CCHInterfaceDictionary.interface_dictionary

class contract_assumption_t
        ?(ppos=[]) ?(spos=[]) (index:int) (callee:int):contract_assumption_int =
object (self)

  val mutable dependent_ppos = ppos
  val mutable dependent_spos = spos

  method add_dependent_ppo (ippo:int) =
    if List.mem ippo dependent_ppos then () else dependent_ppos <- ippo :: dependent_ppos

  method add_dependent_spo (ispo:int) =
    if List.mem ispo dependent_spos then () else dependent_spos <- ispo :: dependent_spos

  method index = index

  method get_xpredicate = id#get_xpredicate index

  method get_callee = callee

  method has_callee = callee >= 0

  method is_global = callee = -1

  method get_dependent_ppos = dependent_ppos

  method get_dependent_spos = dependent_spos

  method toPretty = xpredicate_to_pretty (id#get_xpredicate index)

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    begin
      (if (List.length dependent_ppos) > 0 then
         set "ppos" (String.concat "," (List.map string_of_int dependent_ppos))) ;
      (if (List.length dependent_spos) > 0 then
         set "spos" (String.concat "," (List.map string_of_int dependent_spos))) ;
      seti "ixpre" index ;
      if callee >= 0 then seti "callee" callee
    end

end

let mk_contract_assumption
      ?(ppos=[]) ?(spos=[]) (index:int) (callee:int):contract_assumption_int =
  new contract_assumption_t ~ppos ~spos index callee

                    
let read_xml_contract_assumption (node:xml_element_int) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let index = geti "ixpre" in
  let callee = if has "callee" then geti "callee" else (-1) in
  try
    let ppos =
      if has "ppos" then
        List.map int_of_string (nsplit ',' (get "ppos")) else [] in
    let spos =
      if has "spos" then
        List.map int_of_string (nsplit ',' (get "spos")) else [] in
    mk_contract_assumption ~ppos ~spos index callee
  with
    Failure _ ->
    raise (CCHFailure
             (LBLOCK [ STR "read_xml_contract_assumption: int_of_string on " ;
                       STR (get "ppos") ; STR " and " ; STR (get "spos") ]))

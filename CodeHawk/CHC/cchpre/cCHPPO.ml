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
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHPODictionary
open CCHPreSumTypeSerializer
open CCHPreTypes
open CCHProofObligation

module H = Hashtbl


let contexts = CCHContext.ccontexts
let cdecls = CCHDeclarations.cdeclarations

       
class ppo_manager_t (fname:string) (pod:podictionary_int):ppo_manager_int =
object (self)

  val pod = pod
  val table = H.create 13          (* id -> proof_obligation_int *)

  method add_ppo (loc:location) (ctxt:program_context_int) (p:po_predicate_t) =
    let ppotype = PPOprog (loc,ctxt,p) in
    let index = pod#index_ppo_type ppotype in
    let _ = if H.mem table index then
              ch_error_log#add "multiple ppo's with same id"
                               (LBLOCK [ STR fname ; STR ": " ;
                                         location_to_pretty loc ; STR "; " ;
                                         ctxt#toPretty ]) in
    let ppo = mk_ppo pod ppotype in
    H.add table index ppo

  method add_lib_ppo
           (loc:location) (ctxt:program_context_int) (p:po_predicate_t)
           (fname:string) (pre:xpredicate_t) =
    let ppotype = PPOlib (loc,ctxt,p,fname,pre) in
    let index = pod#index_ppo_type ppotype in
    let ppo = mk_ppo pod ppotype in
    H.add table index ppo

  method get_ppos = H.fold (fun k v r -> v :: r) table []

  method get_ppo (index:int) =
    if H.mem table index then
      H.find table index
    else
      raise (CCHFailure (LBLOCK [ STR "Ppo with index " ; INT index ;
                                  STR " not found" ]))

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun ppo ->
           let pnode = xmlElement "ppo" in
           begin ppo#write_xml pnode ; pnode end) self#get_ppos)

  method read_xml (node:xml_element_int) =
    List.iter (fun pnode ->
        let ppo = read_xml_ppo pnode pod in
        H.add table ppo#index ppo) (node#getTaggedChildren "ppo")

end

let mk_ppo_manager = new ppo_manager_t       

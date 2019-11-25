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
open CHUtils

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHDictionary
open CCHBasicTypes
open CCHExternalPredicate
open CCHFileContract
open CCHFileEnvironment
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHApiAssumption
open CCHContractAssumption
open CCHGlobalAssumption
open CCHPOPredicate
open CCHPostRequest
open CCHPreTypes

module H = Hashtbl
module P = Pervasives

let cd = CCHDictionary.cdictionary
let pd = CCHPredicateDictionary.predicate_dictionary
let id = CCHInterfaceDictionary.interface_dictionary
	
class function_api_t (fname:string):function_api_int =
object (self)

  val api_assumptions = H.create 3
  val contract_assumptions = H.create 3        (* (xpredicate_id,callee_vid) -> contract_assumption *)
  val assumption_requests = H.create 3         (* requests made for (global) assumptions *)
  val postcondition_requests = H.create 3      (* requests made to other functions *)
  val postcondition_guarantees = H.create 3    (* guarantee postconditions of this function *)
  val library_calls = H.create 3
  val missing_summaries = new StringCollections.set_t
  val mutable contractcondition_failures = []
  val unevaluated = H.create 3

  method add_contract_precondition (fdecls:cfundeclarations_int) (ix:int) =    (* xpredicate index *)
    let precondition = id#get_xpredicate ix in
    let pred = xpredicate_to_po_predicate fdecls precondition in
    let predid = pd#index_po_predicate pred in
    if H.mem api_assumptions predid then
      ()
    else
      let a = mk_api_assumption ~isglobal:true predid in
      H.add api_assumptions predid a

  method add_contract_condition_failure (name:string) (desc:string) = 
    contractcondition_failures <- (name,desc) :: contractcondition_failures

  method add_library_call header fname =
    let entry =
      if H.mem library_calls (header,fname) then
        H.find library_calls (header,fname)
      else 0 in
    H.replace library_calls (header,fname) (entry + 1)

  method add_missing_summary name = missing_summaries#add name 
    
  method add_api_assumption
           ?(isfile=false)
           ?(isglobal=false)
           ?(ppos=[])
           ?(spos=[]) (p:po_predicate_t) =
    let index = pd#index_po_predicate p in
    if H.mem api_assumptions index then
      let entry = H.find api_assumptions index in
      begin
        List.iter entry#add_dependent_ppo ppos ;
        List.iter entry#add_dependent_spo spos ;
        Some p
      end
    else
      let p' = self#check_assumptions p in
      match p' with
      | Some p ->
         let index = pd#index_po_predicate p in
         if H.mem api_assumptions index then
           let entry = H.find api_assumptions index in
           begin
             List.iter entry#add_dependent_ppo ppos ;
             List.iter entry#add_dependent_spo spos ;
             Some p
           end
         else
           let a = mk_api_assumption ~isfile ~isglobal ~ppos ~spos index in
           begin
             H.add api_assumptions index a ;
             Some p
           end
      | _ -> None   (* subsumed ? *)

  method private check_assumptions (p:po_predicate_t) =
    let assumptions = H.fold (fun _ v acc -> v::acc) api_assumptions [] in
    check_assumption_predicates (List.map (fun a -> a#get_predicate) assumptions) p

  method add_postcondition_assumption
           ?(ppos=[])
           ?(spos=[])
           (callee:int)
           (pc:xpredicate_t) =
    self#add_contract_assumption ~ppos ~spos callee pc

  method add_global_assumption ?(ppos=[]) ?(spos=[]) (pc:xpredicate_t) =
    self#add_contract_assumption ~ppos ~spos (-1) pc

  method private add_contract_assumption
                   ?(ppos=[])
                   ?(spos=[])
                   (callee:int)
                   (pc:xpredicate_t) =
    let index = id#index_xpredicate pc in
    if H.mem contract_assumptions (index,callee) then
      let entry = H.find contract_assumptions (index,callee) in
      begin
        List.iter entry#add_dependent_ppo ppos;
        List.iter entry#add_dependent_spo spos
      end
    else
      let a = mk_contract_assumption ~ppos ~spos index callee in
      H.add contract_assumptions (index,callee) a

  method add_global_assumption_request ?(ppos=[]) ?(spos=[]) (pc:xpredicate_t) =
    let index = id#index_xpredicate pc in
    if H.mem assumption_requests index then
      let entry = H.find assumption_requests index in
      begin
        List.iter entry#add_dependent_ppo ppos ;
        List.iter entry#add_dependent_spo spos
      end
    else
      let a = mk_global_assumption ~ppos ~spos index in
      H.add assumption_requests index a

  method add_postcondition_request
           ?(ppos=[])
           ?(spos=[])
           (callee:int)
           (pc:xpredicate_t) =
    let request = (callee,pc) in
    let index = id#index_postrequest request in
    if H.mem postcondition_requests index then
      let entry = H.find postcondition_requests index in
      begin
        List.iter entry#add_dependent_ppo ppos ;
        List.iter entry#add_dependent_spo spos
      end
    else
      let r = mk_postcondition_request ~ppos ~spos request in
      H.add postcondition_requests index r

  method add_postcondition_guarantee (pc:xpredicate_t) =
    let index = id#index_xpredicate pc in
    if H.mem postcondition_guarantees index then () else
      H.add postcondition_guarantees index pc

  method add_unevaluated (p:po_predicate_t) (xindex:int) =
    let index = pd#index_po_predicate p in
    let entry =
      if H.mem unevaluated index then
        H.find unevaluated index
      else
        new CHUtils.IntCollections.set_t in
    let _ = entry#add xindex in
    H.replace unevaluated index entry

  method private add_to_table t k v =
    let entry = if H.mem t k then H.find t k else [] in
    H.replace t k (v::entry)
                      
  method get_api_assumption (id:int) =
    if H.mem api_assumptions id then H.find api_assumptions id else
      raise (CCHFailure
               (LBLOCK [ STR "No api assumption found for id " ; INT id ; 
			 STR " in function " ; STR fname ]))
	
  method get_api_assumptions =
    List.sort (fun a1 a2 -> P.compare a1#index a2#index)
              (H.fold (fun _ v r -> v::r) api_assumptions [])

  method get_contract_assumptions =
    List.sort
      (fun a1 a2 ->
        P.compare (a1#index,a1#get_callee) (a2#index,a2#get_callee))
      (H.fold  (fun _ v r -> v::r) contract_assumptions [])

  method get_assumption_requests =
    List.sort (fun a1 a2 -> P.compare a1#index a2#index)
              (H.fold (fun _ v r -> v::r) assumption_requests [])

  method get_postcondition_requests =
    H.fold (fun _ v r -> v::r) postcondition_requests []

  method get_postcondition_guarantees =
    H.fold (fun _ v r -> v::r) postcondition_guarantees []

  method private get_unevaluated =
    List.sort
      (fun (p,_) (q,_) -> P.compare p q)
      (H.fold (fun poid xlist r -> (poid,xlist#toList)::r) unevaluated [])

  method get_library_call_names =
    H.fold (fun (_,fname) _ a -> fname::a) library_calls []

  method get_library_calls =
    H.fold (fun k _ a -> k::a) library_calls []

  method write_xml (node:xml_element_int) =
    let aanode = xmlElement "api-assumptions" in
    let ccnode = xmlElement "contract-assumptions" in
    let hhnode = xmlElement "global-assumption-requests" in
    let ppnode = xmlElement "postcondition-requests" in
    let ggnode = xmlElement "postcondition-guarantees" in
    let llnode = xmlElement "library-calls" in
    let mmnode = xmlElement "missing-summaries" in
    let unode = xmlElement "unevaluated" in
    let xxnode = xmlElement "contract-condition-failures" in
    begin
      (aanode#appendChildren
         (List.map (fun a ->
              let anode = xmlElement "aa" in
              begin
                a#write_xml anode ;
                anode
              end) self#get_api_assumptions)) ;
      (ccnode#appendChildren
         (List.map (fun a ->
              let anode = xmlElement "ca" in
              begin
                a#write_xml anode ;
                anode
              end) self#get_contract_assumptions)) ;
      (hhnode#appendChildren
         (List.map (fun a ->
              let anode = xmlElement "hh" in
              begin
                a#write_xml anode ;
                anode
              end) self#get_assumption_requests)) ;
      (ppnode#appendChildren
         (List.map (fun p ->
              let pnode = xmlElement "rr" in
              begin
                p#write_xml pnode ;
                pnode
              end) self#get_postcondition_requests)) ;
      (ggnode#appendChildren
         (List.map (fun g ->
              let gnode = xmlElement "gg" in
              begin
                id#write_xml_xpredicate gnode g ;
                gnode
              end) self#get_postcondition_guarantees)) ;
      (llnode#appendChildren
         (List.map (fun ((header,fname),count) ->
              let lnode = xmlElement "lc" in
              begin
                lnode#setAttribute "h" header ;
                lnode#setAttribute "f" fname ;
                lnode#setIntAttribute "c" count ;
                lnode
              end) (H.fold (fun k v a -> (k,v)::a) library_calls []))) ;
      (mmnode#appendChildren
         (List.map (fun n ->
              let mnode = xmlElement "ms" in
              begin
                mnode#setAttribute "n" n ;
                mnode
              end) missing_summaries#toList));
      (unode#appendChildren
         (List.map (fun (poid,xlst) ->
              let pnode = xmlElement "uu" in
              begin
                pnode#setIntAttribute "po-id" poid ;
                node#setAttribute "xlst" (String.concat "," (List.map string_of_int xlst)) ;
                pnode
              end) self#get_unevaluated)) ;
      (match contractcondition_failures with
       | [] -> ()
       | l ->
          begin
            xxnode#appendChildren
              (List.map (fun (name,desc) ->
                   let xnode = xmlElement "failure" in
                   begin
                     xnode#setAttribute "name" name ;
                     xnode#setAttribute "desc" desc ;
                     xnode
                   end) l) ;
            node#appendChildren [ xxnode ]
          end) ;
      node#appendChildren
        [ aanode ; ccnode ; hhnode ; ppnode ; ggnode ; llnode ; mmnode ; unode ]
    end
           
  method read_xml (node:xml_element_int) =
    let hasc = node#hasTaggedChild in
    let getcc tag = (node#getTaggedChild tag)#getTaggedChildren in
    begin
      List.iter (fun anode ->
          let a = read_xml_api_assumption anode in
          H.add api_assumptions a#index a) (getcc "api-assumptions" "aa") ;
      List.iter (fun anode ->
          let a = read_xml_contract_assumption anode in
          H.add contract_assumptions
                (a#index,a#get_callee) a)  (getcc "contract-assumptions" "ca") ;                 
      List.iter (fun hnode ->
          let a = read_xml_global_assumption hnode in
          H.add assumption_requests
                a#index a) (getcc "global-assumption-requests" "hh") ;
      List.iter (fun pnode ->
          let r = read_xml_postcondition_request pnode in
          let index = id#index_postrequest r#get_request in
          H.add postcondition_requests
                index r) (getcc "postcondition-requests" "rr") ;
      List.iter (fun gnode ->
          let g = id#read_xml_xpredicate gnode in
          self#add_postcondition_guarantee g)
                (getcc "postcondition-guarantees" "gg") ;
      List.iter (fun lcnode ->
          let header = lcnode#getAttribute "h" in
          let fname = lcnode#getAttribute "f" in
          let count = lcnode#getIntAttribute "c" in
          H.replace library_calls
                    (header,fname) count) (getcc "library-calls" "lc") ;
      List.iter (fun msnode ->
          let name = msnode#getAttribute "n" in
          self#add_missing_summary name) (getcc "missing-summaries" "ms") ;
      (if hasc "contract-condition-failures" then
         List.iter (fun xnode ->
             let name = xnode#getAttribute "name" in
             let desc = xnode#getAttribute "desc" in
             self#add_contract_condition_failure name desc)
                   (getcc "contract-condition-failures" "failure"))
         
    end
      
end
     
let mk_function_api = new function_api_t    

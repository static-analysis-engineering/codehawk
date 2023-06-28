(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt

(* cchlib *)
open CCHBasicTypes
open CCHFileContract
open CCHLibTypes
open CCHUtilities
   
(* cchpre *)
open CCHFunctionAPI
open CCHPODictionary
open CCHPPO
open CCHPreTypes
open CCHSPO

module H = Hashtbl


let id = CCHInterfaceDictionary.interface_dictionary


class proof_scaffolding_t:proof_scaffolding_int =
object (self)

  val apis = H.create 3                     (* fname -> api_assumption_int *)
  val ppos = H.create 3                     (* fname -> ppo_manager_int *)
  val spos = H.create 3                     (* fname -> spo_manager_int *)
  val pods = H.create 3                     (* fname -> podictionary_int *)

  method reset =
    begin
      H.clear apis;
      H.clear ppos;
      H.clear spos;
      H.clear pods;
    end

  method get_function_api (fname:string):function_api_int =
    if H.mem apis fname then
      H.find apis fname
    else
      let api = mk_function_api fname in
      begin
        H.add apis fname api;
        api
      end

  method retrieve_contract_preconditions (fdecls:cfundeclarations_int) (fname:string) =
    let fApi = self#get_function_api fname in
    let gvars = file_contract#get_global_variables in
    begin
      (if file_contract#has_function_contract fname then
         let preconditions =
           (file_contract#get_function_contract fname)#get_precondition_ixs in
         List.iter (fApi#add_contract_precondition fdecls) preconditions);
      (List.iter (fun gvar ->
           begin
             (if gvar.cgv_const then
                match gvar.cgv_value with
                | Some v ->
                   let v = mkNumerical v in
                   let xpred = XRelationalExpr (
                                   Eq, ArgValue (ParGlobal gvar.cgv_name,ArgNoOffset),
                                   NumConstant v) in
                   let xpredix = id#index_xpredicate xpred in
                   fApi#add_contract_precondition fdecls xpredix
               | _ -> ());
             (match gvar.cgv_lb with
              | Some lb ->
                 let lb = mkNumerical lb in
                 let xpred = XRelationalExpr (
                                 Le, ArgValue (ParGlobal gvar.cgv_name,ArgNoOffset),
                                 NumConstant lb) in
                 let xpredix = id#index_xpredicate xpred in
                 fApi#add_contract_precondition fdecls xpredix
              | _ -> ());
             (match gvar.cgv_ub with
              | Some ub ->
                 let ub = mkNumerical ub in
                 let xpred = XRelationalExpr (
                                 Ge, ArgValue (ParGlobal gvar.cgv_name,ArgNoOffset),
                                 NumConstant ub) in
                 let xpredix = id#index_xpredicate xpred in
                 fApi#add_contract_precondition fdecls xpredix
              | _ -> ())
           end) gvars)
    end
                  
                          
      
  method get_ppo_manager (fname:string):ppo_manager_int =
    let pod = self#get_pod fname in
    if H.mem ppos fname then
      H.find ppos fname
    else
      let ppomgr = mk_ppo_manager fname pod in
      begin
        H.add ppos fname ppomgr;
        ppomgr
      end
      
  method get_spo_manager (fname:string):spo_manager_int =
    let pod = self#get_pod fname in
    if H.mem spos fname then
      H.find spos fname
    else
      let spomgr = mk_spo_manager fname pod in
      begin
        H.add spos fname spomgr;
        spomgr
      end

  method get_call_count (fname:string) =
    let spomgr = self#get_spo_manager fname in
    let callsitemgr = spomgr#get_callsite_manager in
    callsitemgr#get_call_count

  method get_direct_callsites (fname:string) =
    let spomgr = self#get_spo_manager fname in
    let callsitemgr = spomgr#get_callsite_manager in
    callsitemgr#get_direct_callsites

  method get_indirect_callsites (fname:string) =
    let spomgr = self#get_spo_manager fname in
    let callsitemgr = spomgr#get_callsite_manager in
    callsitemgr#get_indirect_callsites

  method get_direct_callsite (fname:string) (ctxt:program_context_int) =
    let spomgr = self#get_spo_manager fname in
    let callsitemgr = spomgr#get_callsite_manager in
    callsitemgr#get_direct_callsite ctxt

  method get_indirect_callsite (fname:string) (ctxt:program_context_int) =
    let spomgr = self#get_spo_manager fname in
    let callsitemgr = spomgr#get_callsite_manager in
    callsitemgr#get_indirect_callsite ctxt

  method has_direct_callsite (fname:string) (ctxt:program_context_int) =
    (self#get_spo_manager fname)#get_callsite_manager#has_direct_callsite ctxt

  method has_indirect_callsite (fname:string) (ctxt:program_context_int) =
    (self#get_spo_manager fname)#get_callsite_manager#has_indirect_callsite ctxt
    

  method private get_pod (fname:string) =
    if H.mem pods fname then H.find pods fname else
      raise (CCHFailure
               (LBLOCK [ STR "Proof obligation dictionary for "; STR fname;
                         STR " not found" ]))

  method get_proof_obligations (fname:string) =
    try
      (self#get_ppo_manager fname)#get_ppos @ (self#get_spo_manager fname)#get_spos
    with
    | CCHFailure p ->
       raise (CCHFailure
                (LBLOCK [ STR "Error in get_proof_obligations for "; STR fname ]))

  method write_xml_api (node:xml_element_int) (fname:string) =
    let anode = xmlElement "api" in
    begin
      (self#get_function_api fname)#write_xml anode;
      node#appendChildren [ anode ]
    end

  method read_xml_api (node:xml_element_int) (fname:string) =
    (self#get_function_api fname)#read_xml (node#getTaggedChild "api")

  method write_xml_ppos (node:xml_element_int) (fname:string) =
    let pnode = xmlElement "ppos" in
    begin
      (self#get_ppo_manager fname)#write_xml pnode;
      node#appendChildren [ pnode ]
    end

  method read_xml_ppos (node:xml_element_int) (fname:string) =
    (self#get_ppo_manager fname)#read_xml (node#getTaggedChild "ppos") 

  method write_xml_spos (node:xml_element_int) (fname:string) =
    let snode = xmlElement "spos" in
    begin
      (self#get_spo_manager fname)#write_xml snode;
      node#appendChildren [ snode ]
    end

  method read_xml_spos (node:xml_element_int) (fname:string) =
    (self#get_spo_manager fname)#read_xml (node#getTaggedChild "spos")

  method write_xml_pod (node:xml_element_int) (fname:string) =
    let pod = self#get_pod fname in
    pod#write_xml node

  method read_xml_pod
           (node:xml_element_int) (fname:string) (fdecls:cfundeclarations_int) =
    let pod = mk_podictionary fname fdecls in
    begin
      pod#read_xml node;
      H.replace pods fname pod
    end

  method initialize_pod (fname:string) (fdecls:cfundeclarations_int) =
    H.replace pods fname (mk_podictionary fname fdecls)


end

let proof_scaffolding = new proof_scaffolding_t

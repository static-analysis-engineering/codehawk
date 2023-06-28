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
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHDeclarations
open CCHDictionary
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHCallsite
open CCHPreTypes
open CCHProofObligation
open CCHReturnsite


module H = Hashtbl


class spo_manager_t (fname:string) (pod:podictionary_int):spo_manager_int =
object (self)

  val localspos = H.create 3      (* spo_type_index -> spo *)
  val callsite_manager = mk_callsite_manager fname pod
  val returnsite_manager = mk_returnsite_manager fname pod

  method add_local_spo
           (loc:location) (ctxt:program_context_int) (pred:po_predicate_t) =
    let spotype = LocalSPO (loc,ctxt,pred) in
    let spoid = pod#index_spo_type spotype in
    let spo = mk_local_spo pod spotype in
    if H.mem localspos spoid then () else
      H.add localspos spoid spo

  method add_direct_call
           (loc:location)
           (ctxt:program_context_int)
           ?(header="")
           (callee:varinfo)
           (args:exp list) =
    callsite_manager#add_direct_call loc ctxt ~header callee args

  method add_indirect_call
           (loc:location)
           (ctxt:program_context_int)
           ?(header="")
           (callee:exp)
           (args:exp list) =
    callsite_manager#add_indirect_call loc ctxt ~header callee args

  method add_return (loc:location) (ctxt:program_context_int) (exp:exp option) =
    returnsite_manager#add_return loc ctxt exp

  method create_contract_proof_obligations =
    begin
      callsite_manager#create_contract_proof_obligations;
      returnsite_manager#create_contract_proof_obligations
    end

  method private get_local_spos = H.fold (fun _ v a -> v::a) localspos []

  method get_spo (index:int) =
    try
      List.find  (fun spo -> spo#index = index) self#get_spos
    with
    | Not_found ->
       raise
         (CCHFailure
            (LBLOCK [STR "Spo with index "; INT index; STR " not found"]))

  method get_spos =
    self#get_local_spos @ callsite_manager#get_spos @ returnsite_manager#get_spos

  method get_callsite_manager = callsite_manager

  method private write_xml_local_spos (node:xml_element_int) =
    let spos = self#get_local_spos  in
    node#appendChildren
      (List.map (fun spo ->
           let snode = xmlElement "po"  in
           begin spo#write_xml snode ; snode end) spos)

  method private read_xml_local_spos (node:xml_element_int) =
    List.iter (fun snode ->
        let spo = read_xml_local_spo snode pod in
        H.add localspos spo#index spo) (node#getTaggedChildren "po")

  method write_xml (node:xml_element_int) =
    let lnode = xmlElement "localspos" in
    let cnode = xmlElement "callsites" in
    let rnode = xmlElement "returnsites" in
    begin
      (if H.length localspos > 0 then
         begin
           self#write_xml_local_spos lnode;
           node#appendChildren [lnode]
         end) ;
      callsite_manager#write_xml cnode;
      returnsite_manager#write_xml rnode;
      node#appendChildren [cnode; rnode]
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    let hasc = node#hasOneTaggedChild in
    try
      begin
        (if hasc "localspos" then
           self#read_xml_local_spos (getc "localspos"));
        callsite_manager#read_xml (getc "callsites");
        returnsite_manager#read_xml (getc "returnsites")
      end
    with
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [STR "Failure in spo manager:read_xml: "; STR s]))

end


let mk_spo_manager = new spo_manager_t
             

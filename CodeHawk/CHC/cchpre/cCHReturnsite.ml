(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHTimingLog
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHFileContract
open CCHFileEnvironment
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHPreTypes
open CCHProofObligation
open CCHPOPredicate

module H = Hashtbl


let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations
let id = CCHInterfaceDictionary.interface_dictionary


let create_pc_spos
      (pod:podictionary_int)
      (pcid:int)
      (loc:location)
      (ctxt:program_context_int)
      (exp:exp option) =
  let postcondition = id#get_xpredicate pcid in
  let pred =
    xpredicate_to_po_predicate ~returnexp:exp pod#fdecls postcondition  in
  let spotype = ReturnsiteSPO (loc,ctxt,pred,postcondition) in
  mk_returnsite_spo pod spotype


class returnsite_t
        (pod:podictionary_int)
        ?(pcspos:(int * proof_obligation_int list) list=[])
        (loc:location)
        (ctxt:program_context_int)
        (exp:exp option) =
object (self)

  val spos = H.create 3      (* xpredicate id -> spo list *)

  initializer
    List.iter (fun (k, v) ->
        match v with
        | [] ->
           (try
              H.add spos k [(create_pc_spos pod k loc ctxt exp)]
            with
            | CCHFailure p -> ch_error_log#add "postcondition" p)
        | _ -> H.add spos k v) pcspos

  method add_postcondition (index:int) =
    match id#get_xpredicate index with
    | XTainted _ -> ()
    | _ ->
       begin
         log_info "add postcondition %d [%s:%d]" index __FILE__ __LINE__;
         (if H.mem spos index then
            ()
          else
            H.add spos index [(create_pc_spos pod index loc ctxt exp)])
       end

  method add_preservation_condition (gv: globalvar_contract_int) =
    let gvar = file_environment#get_globalvar_by_name gv#get_name in
    let gexp = Lval (Var (gvar.vname, gvar.vid), NoOffset) in
    let pred = PValuePreserved gexp in
    let xpred =
      XPreservesValue (ArgValue (ParGlobal gv#get_name,ArgNoOffset)) in
    let xpredix = id#index_xpredicate xpred in
    if H.mem spos xpredix then
      ()
    else
      let spotype = ReturnsiteSPO (loc, ctxt, pred, xpred) in
      H.add spos xpredix [(mk_returnsite_spo pod spotype)]

  method add_notnull_condition (gv: globalvar_contract_int) =
    let gvar = file_environment#get_globalvar_by_name gv#get_name in
    let gexp = Lval (Var (gvar.vname, gvar.vid), NoOffset) in
    let pred = PNotNull gexp in
    let xpred = XNotNull (ArgValue (ParGlobal gv#get_name,ArgNoOffset)) in
    let xpredix = id#index_xpredicate xpred in
    let spotype = ReturnsiteSPO (loc, ctxt, pred, xpred) in
    if H.mem spos xpredix then
      ()
    else
      H.add spos xpredix [(mk_returnsite_spo pod spotype)]

  method add_inequality_condition
           (gv: globalvar_contract_int) (op: binop) (lb: int) =
    let gvar = file_environment#get_globalvar_by_name gv#get_name in
    let gexp = Lval (Var (gvar.vname, gvar.vid), NoOffset) in
    let lbexp = Const (CInt (Int64.of_int lb, IInt, None)) in
    let pred = PValueConstraint (BinOp (op, gexp, lbexp, TInt (IInt, []))) in
    let xpred =
      XRelationalExpr
        (op,
         ArgValue (ParGlobal gv#get_name,ArgNoOffset),
         NumConstant (mkNumerical lb)) in
    let xpredix = id#index_xpredicate xpred in
    let spotype = ReturnsiteSPO (loc, ctxt, pred, xpred) in
    if H.mem spos xpredix then
      ()
    else
      H.add spos xpredix [(mk_returnsite_spo pod spotype)]

  method get_location = loc

  method get_context = ctxt

  method get_exp =
    match exp with
    | Some e -> e
    | _ ->
       raise
         (CCHFailure (LBLOCK [STR "Returnsite does not have an expression"]))

  method has_exp = match exp with Some _ -> true | _ -> false

  method get_spos = H.fold (fun _ v r -> v@r) spos []

  method private get_spo_lists = H.fold (fun k v r -> (k,v)::r) spos []

  method write_xml (node:xml_element_int) =
    let ppnode = xmlElement "post-guarantees" in
    begin
      ppnode#appendChildren
        (List.map (fun (pcid,spos) ->
             let pnode = xmlElement "pc" in
             begin
               pnode#appendChildren
                 (List.map (fun spo ->
                      let snode = xmlElement "po" in
                      begin
                        spo#write_xml snode;
                        snode
                      end) spos);
               pnode#setIntAttribute "iipc" pcid;
               pnode
           end) self#get_spo_lists);
       node#appendChildren [ppnode];
       cdecls#write_xml_location node loc;
       ccontexts#write_xml_context node ctxt;
       cd#write_xml_exp_opt node exp
    end

end


let read_xml_returnsite
      (node:xml_element_int) (pod:podictionary_int):returnsite_t =
  let exp = cd#read_xml_exp_opt node in
  let loc = cdecls#read_xml_location node in
  let ctxt = ccontexts#read_xml_context node in
  let pcspos = H.create 3 in
  let _ =
    List.iter
      (fun pnode ->
        let spos =
          List.map
            (fun snode -> read_xml_returnsite_spo snode pod)
            (pnode#getTaggedChildren "po") in
        let pcid = pnode#getIntAttribute "iipc" in
        H.add pcspos pcid spos)
      ((node#getTaggedChild "post-guarantees")#getTaggedChildren "pc") in
  let pcspos = H.fold (fun k v a -> (k,v)::a) pcspos [] in
  new returnsite_t pod ~pcspos loc ctxt exp


class returnsite_manager_t
        (fname:string) (pod:podictionary_int):returnsite_manager_int =
object

  val returnsites = H.create 1
  val postconditions = new CHUtils.IntCollections.set_t

  method add_return
           (loc:location) (ctxt:program_context_int) (exp:exp option) =
    let ictxt = ccontexts#index_context ctxt in
    let returnsite = new returnsite_t pod loc ctxt exp in
    H.add returnsites ictxt returnsite

  method get_postconditions =
    List.map id#get_xpredicate postconditions#toList

  method create_contract_proof_obligations =
    let _ =
      log_info
        "create contract postcondition proof obligations [%s:%d]"
        __FILE__ __LINE__ in
    begin
      if file_contract#has_function_contract fname then
        begin
          postconditions#addList
            (file_contract#get_function_contract fname)#get_postcondition_ixs;
          postconditions#iter (fun pcid ->
              H.iter (fun _ v -> v#add_postcondition pcid) returnsites)
        end
    end

  method get_spos =
    List.concat (H.fold (fun _ v r -> v#get_spos::r) returnsites [])

  method write_xml (node:xml_element_int) =
    let _ =
      log_info
        "write returnsite proof obligations: %d [%s:%d]"
        (H.length returnsites)
        __FILE__ __LINE__ in
    begin
      node#appendChildren
        (List.map (fun r ->
             let rnode = xmlElement "rs" in
             begin
               r#write_xml rnode;
               rnode
             end)
           (H.fold (fun _ v r -> v::r) returnsites []))
    end

  method read_xml (node:xml_element_int) =
    try
      List.iter (fun rnode ->
          let r = read_xml_returnsite rnode pod in
          let ictxt = ccontexts#index_context r#get_context in
          H.add returnsites ictxt r) (node#getTaggedChildren "rs")
    with
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [STR "Failure in returnsite manager:read_xml: "; STR s]))

end


let mk_returnsite_manager = new returnsite_manager_t

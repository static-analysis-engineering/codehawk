(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHIndexTable
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHDictionary
open CCHLibTypes
open CCHSumTypeSerializer
open CCHUtilities

(* cchpre *)
open CCHPreSumTypeSerializer
open CCHPreTypes

module H = Hashtbl


let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations
let pd = CCHPredicateDictionary.predicate_dictionary
let id = CCHInterfaceDictionary.interface_dictionary
let contexts = CCHContext.ccontexts

let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [ STR "Type " ; STR name ; STR " tag: " ; STR tag ;
             STR " not recognized. Accepted tags: " ;
             pretty_print_list accepted (fun s -> STR s) "" ", " "" ] in
  begin
    ch_error_log#add "serialization tag" msg ;
    raise (CCHFailure msg)
  end


class podictionary_t
        (fname:string) (fdecls:cfundeclarations_int):podictionary_int =
object (self)

  val assumption_table = mk_index_table "assumption-table"
  val ppo_type_table = mk_index_table "ppo-type-table"
  val spo_type_table = mk_index_table "spo-type-table"
                  
  val mutable tables = []

  initializer
    tables <- [
      assumption_table ;
      ppo_type_table ;
      spo_type_table 
    ]

  method fdecls = fdecls

  method index_assumption (a:assumption_type_t) =
    let tags = [ assumption_type_mcts#ts a ] in
    let key = match a with
      | LocalAssumption pred -> (tags,[pd#index_po_predicate pred ])
      | ApiAssumption pred -> (tags,[pd#index_po_predicate pred ])
      | GlobalApiAssumption pred -> (tags,[pd#index_po_predicate pred])
      | PostAssumption (i,x) -> (tags,[i; id#index_xpredicate x ])
      | GlobalAssumption x -> (tags,[id#index_xpredicate x ]) in
    assumption_table#add key

  method get_assumption (index:int):assumption_type_t =
    let name = "assumption_type" in
    let (tags,args) = assumption_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "la" -> LocalAssumption (pd#get_po_predicate (a 0))
    | "aa" -> ApiAssumption (pd#get_po_predicate (a 0))
    | "gi" -> GlobalApiAssumption (pd#get_po_predicate (a 0))
    | "ca" -> PostAssumption (a 0,id#get_xpredicate (a 1))
    | "ga" -> GlobalAssumption (id#get_xpredicate (a 0))
    | s -> raise_tag_error name s assumption_type_mcts#tags

  method index_ppo_type (p:ppo_type_t) =
    let tags = [ ppo_type_mcts#ts p ] in
    let key = match p with
      | PPOprog (loc,ctxt,pred) ->
         (tags,[ cdecls#index_location loc ;
                 contexts#index_context ctxt ;
                 pd#index_po_predicate pred ])
      | PPOlib (loc,ctxt,pred,fname,pre) ->
         (tags @ [ fname ],
          [ cdecls#index_location loc ; contexts#index_context ctxt ;
            pd#index_po_predicate pred ; id#index_xpredicate pre ]) in
    ppo_type_table#add key

  method get_ppo_type (index:int):ppo_type_t =
    let name = "ppo_type" in
    let (tags,args) = ppo_type_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "p" ->
       PPOprog (cdecls#get_location (a 0), contexts#get_context (a 1),
                pd#get_po_predicate (a 2))
    | "pl" ->
       PPOlib (cdecls#get_location (a 0), contexts#get_context (a 1),
               pd#get_po_predicate (a  2), t 1, id#get_xpredicate (a 3))
    | s -> raise_tag_error name s ppo_type_mcts#tags

  method index_spo_type (s:spo_type_t) =
    let tags = [ spo_type_mcts#ts s ] in
    let key = match s with
      | LocalSPO (loc,ctxt,pred) ->
         (tags,[ cdecls#index_location loc ; contexts#index_context ctxt ;
                 pd#index_po_predicate pred ])
      | CallsiteSPO (loc,ctxt,pred,apiid) ->
         (tags,[ cdecls#index_location loc ; contexts#index_context ctxt ;
                 pd#index_po_predicate pred ; apiid ])
      | ReturnsiteSPO (loc,ctxt,pred,pc) ->
         (tags, [ cdecls#index_location loc ; contexts#index_context ctxt ;
                  pd#index_po_predicate pred ; id#index_xpredicate pc ]) in
    spo_type_table#add key

  method get_spo_type (index:int) =
    let name = "spo_type" in
    let (tags,args) = spo_type_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "ls" ->
       LocalSPO (
           cdecls#get_location (a 0),
           contexts#get_context (a 1),
           pd#get_po_predicate (a 2))
    | "cs" ->
       CallsiteSPO (
           cdecls#get_location (a 0),
           contexts#get_context (a 1),
           pd#get_po_predicate (a 2),
           a 3)
    | "rs" ->
       ReturnsiteSPO (
           cdecls#get_location (a 0),
           contexts#get_context (a 1),
           pd#get_po_predicate (a 2),
           id#get_xpredicate (a 3))
    | s -> raise_tag_error name s spo_type_mcts#tags

  method write_xml_assumption
           ?(tag="iast") (node:xml_element_int) (a:assumption_type_t) =
    node#setIntAttribute tag (self#index_assumption a)

  method read_xml_assumption
           ?(tag="iast") (node:xml_element_int):assumption_type_t =
    self#get_assumption (node#getIntAttribute tag)

  method write_xml_ppo_type
           ?(tag="ippo") (node:xml_element_int) (p:ppo_type_t) =
    node#setIntAttribute tag (self#index_ppo_type p)

  method read_xml_ppo_type
           ?(tag="ippo") (node:xml_element_int):ppo_type_t =
    self#get_ppo_type (node#getIntAttribute tag)

  method write_xml_spo_type
           ?(tag="ispo") (node:xml_element_int) (s:spo_type_t) =
    node#setIntAttribute tag (self#index_spo_type s)

  method read_xml_spo_type
           ?(tag="ispo") (node:xml_element_int):spo_type_t =
    self#get_spo_type (node#getIntAttribute tag)
    
  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin t#write_xml tnode ; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK (
        List.map (fun t ->
            LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let mk_podictionary = new podictionary_t

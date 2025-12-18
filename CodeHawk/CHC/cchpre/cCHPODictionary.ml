(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHUtilities

(* cchpre *)
open CCHPreSumTypeSerializer
open CCHPreTypes

module H = Hashtbl
module TR = CHTraceResult

let (let* ) x f = CHTraceResult.tbind f x

let cdecls = CCHDeclarations.cdeclarations
let cd = CCHDictionary.cdictionary
let pd = CCHPredicateDictionary.predicate_dictionary
let id = CCHInterfaceDictionary.interface_dictionary
let contexts = CCHContext.ccontexts

let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)

let elocm
      (line: int)
      (table: string)
      (tag: string)
      (available_tags: string list): string =
  (eloc line)
  ^ ": podictionary. invalid tag in table: "
  ^ table
  ^ ": "
  ^ tag
  ^ " (available tags: "
  ^ (String.concat ", " available_tags)


let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [
        STR "Type ";
        STR name; STR " tag: ";
        STR tag;
        STR " not recognized. Accepted tags: ";
        pretty_print_list accepted (fun s -> STR s) "" ", " ""] in
  begin
    ch_error_log#add "serialization tag" msg;
    raise (CCHFailure msg)
  end


class podictionary_t
        (_fname:string) (fdecls:cfundeclarations_int):podictionary_int =
object (self)

  val output_parameter_rejection_reason_table =
    mk_index_table "output-parameter-rejection-reason-table"
  val output_parameter_status_table = mk_index_table "output-parameter-status-table"
  val assumption_table = mk_index_table "assumption-table"
  val ppo_type_table = mk_index_table "ppo-type-table"
  val spo_type_table = mk_index_table "spo-type-table"

  val mutable tables = []

  initializer
    tables <- [
      output_parameter_rejection_reason_table;
      output_parameter_status_table;
      assumption_table;
      ppo_type_table;
      spo_type_table
   ]

  method fdecls = fdecls

  method index_output_parameter_rejection_reason
           (r: output_parameter_rejection_reason_t) =
    let tags = [output_parameter_rejection_reason_mcts#ts r] in
    let key = match r with
      | OpConstQualifier ty -> (tags, [cd#index_typ ty])
      | OpSystemStruct cinfo -> (tags, [cdecls#index_compinfo cinfo])
      | OpArrayStruct cinfo -> (tags, [cdecls#index_compinfo cinfo])
      | OpArrayType ty -> (tags, [cd#index_typ ty])
      | OpVoidPointer -> (tags, [])
      | OpPointerPointer ty -> (tags, [cd#index_typ ty])
      | OpParameterRead linenumber -> (tags, [linenumber])
      | OpOtherReason reason -> (tags, [cd#index_string reason]) in
    output_parameter_rejection_reason_table#add key

  method get_output_parameter_rejection_reason (index: int):
           output_parameter_rejection_reason_t traceresult =
    let name = "output_parameter_rejection_reason" in
    let (tags, args) = output_parameter_rejection_reason_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "a" -> Ok (OpArrayStruct (cdecls#get_compinfo (a 0)))
    | "at" -> Ok (OpArrayType (cd#get_typ (a 0)))
    | "c" -> Ok (OpConstQualifier (cd#get_typ (a 0)))
    | "o" -> Ok (OpOtherReason (cd#get_string (a 0)))
    | "p" -> Ok (OpPointerPointer (cd#get_typ (a 0)))
    | "r" -> Ok (OpParameterRead (a 0))
    | "s" -> Ok (OpSystemStruct (cdecls#get_compinfo (a 0)))
    | "v" -> Ok OpVoidPointer
    | s -> Error [elocm __LINE__ name s output_parameter_rejection_reason_mcts#tags]

  method index_output_parameter_status (s: output_parameter_status_t) =
    let tags = [output_parameter_status_mcts#ts s] in
    let key = match s with
      | OpUnknown -> (tags, [])
      | OpRejected rs ->
         (tags, (List.map self#index_output_parameter_rejection_reason rs))
      | OpViable -> (tags, [])
      | OpWritten -> (tags, [])
      | OpUnaltered -> (tags, []) in
    output_parameter_status_table#add key

  method get_output_parameter_status (index: int):
           output_parameter_status_t traceresult =
    let name = "output_parameter_status" in
    let (tags, args) = output_parameter_status_table#retrieve index in
    let t = t name tags in
    match (t 0) with
    | "u" -> Ok OpUnknown
    | "v" -> Ok OpViable
    | "w" -> Ok OpWritten
    | "a" -> Ok OpUnaltered
    | "r" ->
       let* reasons =
         TR.tbind_map_list self#get_output_parameter_rejection_reason args in
       Ok (OpRejected reasons)
    | s -> Error [elocm __LINE__ name s output_parameter_status_mcts#tags]

  method index_assumption (a:assumption_type_t) =
    let tags = [assumption_type_mcts#ts a] in
    let key = match a with
      | LocalAssumption pred -> (tags, [pd#index_po_predicate pred])
      | ApiAssumption pred -> (tags, [pd#index_po_predicate pred])
      | GlobalApiAssumption pred -> (tags, [pd#index_po_predicate pred])
      | PostAssumption (i, x) -> (tags,[i; id#index_xpredicate x])
      | GlobalAssumption x -> (tags, [id#index_xpredicate x]) in
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
    | "ca" -> PostAssumption (a 0, id#get_xpredicate (a 1))
    | "ga" -> GlobalAssumption (id#get_xpredicate (a 0))
    | s -> raise_tag_error name s assumption_type_mcts#tags

  method index_ppo_type (p:ppo_type_t) =
    let tags = [ppo_type_mcts#ts p] in
    let key = match p with
      | PPOprog (loc, ctxt, pred) ->
         (tags,
          [cdecls#index_location loc;
           contexts#index_context ctxt;
           pd#index_po_predicate pred])
      | PPOlib (loc, ctxt, pred, fname, pre) ->
         (tags @ [fname],
          [cdecls#index_location loc;
           contexts#index_context ctxt;
           pd#index_po_predicate pred;
           id#index_xpredicate pre]) in
    ppo_type_table#add key

  method get_ppo_type (index:int):ppo_type_t =
    let name = "ppo_type" in
    let (tags,args) = ppo_type_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "p" ->
       PPOprog
         (cdecls#get_location (a 0),
          contexts#get_context (a 1),
          pd#get_po_predicate (a 2))
    | "pl" ->
       PPOlib
         (cdecls#get_location (a 0),
          contexts#get_context (a 1),
          pd#get_po_predicate (a  2),
          t 1,
          id#get_xpredicate (a 3))
    | s -> raise_tag_error name s ppo_type_mcts#tags

  method index_spo_type (s:spo_type_t) =
    let tags = [spo_type_mcts#ts s] in
    let key = match s with
      | LocalSPO (loc,ctxt,pred) ->
         (tags,
          [cdecls#index_location loc;
           contexts#index_context ctxt;
           pd#index_po_predicate pred])
      | CallsiteSPO (loc, ctxt, pred, apiid) ->
         (tags,
          [cdecls#index_location loc;
           contexts#index_context ctxt;
           pd#index_po_predicate pred;
           apiid])
      | ReturnsiteSPO (loc, ctxt, pred, pc) ->
         (tags,
          [cdecls#index_location loc;
           contexts#index_context ctxt;
           pd#index_po_predicate pred;
           id#index_xpredicate pc]) in
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

  method write_xml_output_parameter_status
           ?(tag="icops") (node: xml_element_int) (s: output_parameter_status_t) =
    node#setIntAttribute tag (self#index_output_parameter_status s)

  method read_xml_output_parameter_status
           ?(tag="icops") (node: xml_element_int):
           output_parameter_status_t traceresult =
    self#get_output_parameter_status (node#getIntAttribute tag)

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
           begin t#write_xml tnode; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK (
        List.map (fun t ->
            LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let mk_podictionary = new podictionary_t

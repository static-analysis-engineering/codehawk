(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHPreAPI
open JCHPreSumTypeSerializer

module H = Hashtbl


class cgdictionary_t:cgdictionary_int =
object (self)

  val target_table = mk_index_table "target-table"

  val mutable tables = []

  initializer
    tables <- [
      target_table;
   ]

  method index_target (e:call_targets_t) =
    let tags = [call_targets_mcts#ts e] in
    let key = match e with
      | NonVirtualTarget (ty,cmsix) ->
         (tags @ [non_virtual_target_type_mfts#ts ty],[cmsix])
      | ConstrainedVirtualTargets (name,l) -> (tags @ [name], l)
      | VirtualTargets l -> (tags, l)
      | EmptyTarget (is_interface,cn,ms) ->
         (tags,[if is_interface then 1 else 0; cn#index; ms#index]) in
    target_table#add key

  method get_target (index:int) =
    let (tags,args) = target_table#retrieve index in
    let t = t "edge" tags in
    let a = a "edge" args in
    match (t 0) with
    | "nv" -> NonVirtualTarget (non_virtual_target_type_mfts#fs (t 1), a 0)
    | "cv" -> ConstrainedVirtualTargets (t 1, args)
    | "v" -> VirtualTargets args
    | "empty" -> EmptyTarget ((a 0) = 1, retrieve_cn (a 1), retrieve_ms (a 2))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "target tag "; STR s; STR " not recognized"]))

  method write_xml_target
           ?(tag="itgt") (node:xml_element_int) (e:call_targets_t) =
    node#setIntAttribute tag (self#index_target e)

  method read_xml_target ?(tag="itgt") (node:xml_element_int):call_targets_t =
    self#get_target (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables;

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let cgdictionary = new cgdictionary_t

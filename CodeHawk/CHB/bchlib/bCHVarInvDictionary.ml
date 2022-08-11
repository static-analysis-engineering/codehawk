(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open CHXmlDocument

(* xprlib *)
open XprDictionary

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHSumTypeSerializer


let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [
        STR "Type ";
        STR name;
        STR " tag: ";
        STR tag;
        STR " not recognized. Accepted tags: ";
        pretty_print_list accepted (fun s -> STR s) "" ", " ""] in
  begin
    ch_error_log#add "serialization tag" msg ;
    raise (BCH_failure msg)
  end


class varinvdictionary_t (vard: vardictionary_int): varinvdictionary_int =
object (self)

  val vard = vard
  val vardefuse_table = mk_index_table "vardefuse-table"
  val var_invariant_fact_table = mk_index_table "var-invariant-fact-table"
  val mutable tables = []

  initializer
    tables <- [
      vardefuse_table;
      var_invariant_fact_table
    ]

  method xd = vard#xd

  method index_var_def_use ((v, sl): vardefuse_t): int =
    vardefuse_table#add
      ([], (self#xd#index_variable v) :: List.map self#xd#index_symbol sl)

  method get_var_def_use (index: int): vardefuse_t =
    let (_, args) = vardefuse_table#retrieve index in
    (self#xd#get_variable (List.hd args),
     List.map self#xd#get_symbol (List.tl args))

  method index_var_invariant_fact (f: var_invariant_fact_t): int =
    let tags = [var_invariant_fact_mcts#ts f] in
    let key =
      match f with
      | ReachingDef d -> (tags, [self#index_var_def_use d])
      | FlagReachingDef d -> (tags, [self#index_var_def_use d])
      | DefUse d -> (tags, [self#index_var_def_use d])
      | DefUseHigh d -> (tags, [self#index_var_def_use d]) in
    var_invariant_fact_table#add key

  method get_var_invariant_fact (index: int): var_invariant_fact_t =
    let name = "var_invariant_fact" in
    let (tags, args) = var_invariant_fact_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "r" -> ReachingDef (self#get_var_def_use (a 0))
    | "f" -> FlagReachingDef (self#get_var_def_use (a 0))
    | "d" -> DefUse (self#get_var_def_use (a 0))
    | "h" -> DefUseHigh (self#get_var_def_use (a 0))
    | s -> raise_tag_error name s var_invariant_fact_mcts#tags

  method write_xml_var_invariant_fact
           ?(tag="vif") (node: xml_element_int) (f: var_invariant_fact_t) =
    node#setIntAttribute tag (self#index_var_invariant_fact f)

  method read_xml_var_invariant_fact
           ?(tag="vif") (node: xml_element_int): var_invariant_fact_t =
    self#get_var_invariant_fact (node#getIntAttribute tag)

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end
                            

let mk_varinvdictionary = new varinvdictionary_t

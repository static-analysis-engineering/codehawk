(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHIndexTable
open CHLogger
open CHXmlDocument

(* xprlib *)
open XprDictionary

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHSumTypeSerializer


let bcd = BCHBCDictionary.bcdictionary
let bd = BCHDictionary.bdictionary

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
    ch_error_log#add "serialization tag" msg;
    raise (BCH_failure msg)
  end


class tinvdictionary_t (vard:vardictionary_int):tinvdictionary_int =
object (self)

  val vard = vard
  val type_invariant_fact_table = mk_index_table "type-invariant-fact-table"
  val mutable tables = []

  initializer
    tables <- [
      type_invariant_fact_table
    ]

  method xd = vard#xd

  method index_type_invariant_fact (f: type_invariant_fact_t) =
    let tags = [ type_invariant_fact_mcts#ts f ] in
    let key = match f with
      | VarTypeFact (v, t, sl) ->
         (tags,
          [self#xd#index_variable v; bcd#index_typ t]
          @ (List.map bd#index_string sl))
      | ConstTypeFact (n, t) -> (tags @ [n#toString], [bcd#index_typ t])
      | XprTypeFact (x, t) -> (tags,[self#xd#index_xpr x; bcd#index_typ t]) in
    type_invariant_fact_table#add key

  method get_type_invariant_fact (index:int) =
    let name = type_invariant_fact_mcts#name in
    let (tags,args) = type_invariant_fact_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "v" ->
       VarTypeFact
         (self#xd#get_variable (a 0),
          bcd#get_typ (a 1),
          List.map bd#get_string (get_list_suffix args 2))
    | "c" ->
       ConstTypeFact (mkNumericalFromString (t 1), bcd#get_typ (a 0))
    | "x" ->
       XprTypeFact (self#xd#get_xpr (a 0), bcd#get_typ (a 1))
    | s -> raise_tag_error name s type_invariant_fact_mcts#tags

  method write_xml_type_invariant_fact
           ?(tag="itf") (node:xml_element_int) (f:type_invariant_fact_t) =
    node#setIntAttribute tag (self#index_type_invariant_fact f)

  method read_xml_type_invariant_fact
           ?(tag="itf") (node:xml_element_int):type_invariant_fact_t =
    self#get_type_invariant_fact (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map (fun t ->
           let tnode = xmlElement t#get_name in
           begin t#write_xml tnode; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK (List.map (fun t ->
                LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let mk_tinvdictionary = new tinvdictionary_t

    

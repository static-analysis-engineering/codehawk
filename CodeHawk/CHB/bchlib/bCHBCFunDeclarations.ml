(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs LLC

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


(* chutil *)
open CHIndexTable
open CHXmlDocument

(* bchlib *)
open BCHBCSumTypeSerializer
open BCHBCTypes


let bcd = BCHBCDictionary.bcdictionary

let ibool b = if b then 1 else 0


class bcfundeclarations_t: bcfundeclarations_int =
object (self)

  val local_varinfo_table = mk_index_table "local-varinfo-table"
  val mutable tables = []

  initializer
    tables <- [local_varinfo_table]

  method private index_varinfo (vinfo: bvarinfo_t) (formalseqnr: int) =
    let tags = [vinfo.bvname; storage_mfts#ts vinfo.bvstorage] in
    let args = [
        vinfo.bvid;
        bcd#index_typ vinfo.bvtype;
        bcd#index_attributes vinfo.bvattr;
        ibool vinfo.bvglob;
        ibool vinfo.bvinline; bcd#index_location vinfo.bvdecl;
        ibool vinfo.bvaddrof;
        formalseqnr] in
    (tags,args)

  method private get_varinfo (index: int): bvarinfo_t =
    let name = "bvarinfo_t" in
    let (tags, args) = local_varinfo_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    {
      bvname = (t 0);
      bvstorage = storage_mfts#fs (t 1);
      bvid = (a 0);
      bvinit = None;
      bvtype = bcd#get_typ (a 1);
      bvattr = bcd#get_attributes (a 2);
      bvglob = (a 3) = 1;
      bvinline = (a 4) = 1;
      bvdecl = bcd#get_location (a 5);
      bvaddrof = (a 6) = 1;
      bvparam = (a 7)
    }

  method index_formal (vinfo: bvarinfo_t) (seqnr: int) =
    local_varinfo_table#add (self#index_varinfo vinfo seqnr)

  method index_local (vinfo: bvarinfo_t) =
    local_varinfo_table#add (self#index_varinfo vinfo 0)

  method write_xml_formal
           ?(tag="f") (node: xml_element_int) (vinfo: bvarinfo_t) (seqnr: int) =
    node#setIntAttribute tag (self#index_formal vinfo seqnr)

  method write_xml_local ?(tag="l") (node: xml_element_int) (vinfo: bvarinfo_t) =
    node#setIntAttribute tag (self#index_local vinfo)

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
    local_varinfo_table#read_xml (getc "local-varinfo-table")

end


let mk_bcfundeclarations () = new bcfundeclarations_t
    

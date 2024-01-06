(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* cil *)
open GoblintCil

(* chutil *)
open CHIndexTable
open CHXmlDocument

(* chcil *)
open CHCilSumTypeSerializer
open CHCilTypes
      
let cd = CHCilDictionary.cildictionary
let cdecls = CHCilDeclarations.cildeclarations

let ibool b = if b then 1 else 0

class cilfundeclarations_t: cilfundeclarations_int =
object (self)

  val local_varinfo_table = mk_index_table "local-varinfo-table"
  val mutable tables = []

  initializer
    tables <- [local_varinfo_table]

  method private getrep (vinfo: varinfo) (formalseqnr: int) =
    let tags = [vinfo.vname; storage_mfts#ts vinfo.vstorage] in
    let args =
      [vinfo.vid;
       cd#index_typ vinfo.vtype;
       cd#index_attributes vinfo.vattr;
       ibool vinfo.vglob;
       ibool vinfo.vinline;
       cdecls#index_location vinfo.vdecl;
       ibool vinfo.vaddrof;
       formalseqnr] in
    (tags, args)

  method index_formal (vinfo: varinfo) (seqnr: int) =
    local_varinfo_table#add (self#getrep vinfo seqnr)

  method index_local (vinfo: varinfo) =
    local_varinfo_table#add (self#getrep vinfo 0)

  method write_xml_formal
           ?(tag="f") (node: xml_element_int) (vinfo: varinfo) (seqnr: int) =
    node#setIntAttribute tag (self#index_formal vinfo seqnr)

  method write_xml_local ?(tag="l") (node: xml_element_int) (vinfo: varinfo) =
    node#setIntAttribute tag (self#index_local vinfo)

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

end

let mk_cilfundeclarations () = new cilfundeclarations_t
    

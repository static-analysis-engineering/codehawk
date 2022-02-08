(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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
open CHCommon
open CHPretty

(* chutil *)
open CHUtil
open CHXmlDocument
   
module H = Hashtbl


class type string_index_table_int =
  object
    method reset: unit
    method add: string -> int
    method retrieve: int -> string
    method values: string list
    method items: (string * int) list
    method size: int
    method get_name: string
    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit
  end


let reportstring_maxlength = 20


let encode_string = CHUtil.encode_string
let decode_string = CHUtil.decode_string

  
class string_index_table_t (name:string):string_index_table_int =
object (self)

  val mutable next = 1
  val table = H.create 3        (* string -> index *)
  val revtable = H.create 3     (* index -> string *)

  method reset =
    begin
      next <- 1 ;
      H.clear table ;
      H.clear revtable
    end

  method get_name = name

  method add (s:string) =
    if H.mem table s then
      H.find table s
    else
      let index = next in
      begin
        H.add table s index ;
        H.add revtable index s ;
        next <- next + 1 ;
        index
      end

  method retrieve (index:int) =
    try
      H.find revtable index
    with
    | Not_found ->
       raise (CHFailure
                (LBLOCK [ STR "Index " ; INT index ;
                          STR " not found in string table" ]))

  method values = H.fold (fun k _ r -> k :: r) table []

  method items = H.fold (fun k index r -> (k,index) :: r) table []

  method private get_indexed_keys =
    List.sort Stdlib.compare (H.fold (fun k v r -> (k,v) :: r) revtable [])

  method size = H.length table

  method read_xml (node:xml_element_int) =
    let maxcount = ref 0 in
    begin
      List.iter (fun snode ->
          let get = snode#getAttribute in
          let geti = snode#getIntAttribute in
          let has = snode#hasNamedAttribute in
          let index = geti "ix" in
          let ishex = has "hex" && (get "hex" = "y") in
          let s = decode_string (ishex, (get "v")) in
          begin
            H.add table s index ;
            H.add revtable index s ;
            if index > !maxcount then maxcount := index
          end) (node#getTaggedChildren "n") ;
      next <- !maxcount + 1
    end

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map (fun (index,s) ->
           let snode = xmlElement "n" in
           let set = snode#setAttribute in
           let seti = snode#setIntAttribute in
           let (ishex,encoding) = encode_string s in
           let len = String.length s in
           begin
             (if ishex then set "hex" "y") ;
             seti "ix" index ;
             seti "len" len ;
             set "v" encoding ;
             snode
           end) self#get_indexed_keys)
end

let mk_string_index_table = new string_index_table_t

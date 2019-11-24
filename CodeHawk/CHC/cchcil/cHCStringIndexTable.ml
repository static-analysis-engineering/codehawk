(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* cchcil *)
open CHPrettyPrint
open CHUtilities
open CHXml
   
module H = Hashtbl
module P = Pervasives

class type string_index_table_int =
  object
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

let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l

let value_from_byte (b:int) =
  if b >= 48 && b < 58 then
    b - 48
  else if b >= 97 && b < 103 then
    b - 87
  else
    raise (CCFailure (LBLOCK [ STR "Unexpected value in value_from_byte: " ; INT b ]))
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
    !h
  end

let dehex_string (h:string) =
  let ch = IO.input_string h in
  let len = String.length h in
  let s = ref "" in
  begin
    for i = 0 to (len/2) - 1 do
      let b1 = value_from_byte (IO.read_byte ch) in
      let b2 = value_from_byte (IO.read_byte ch) in
      let ich = b1 * 16 + b2 in
      if ich > 255 then
        begin
          pr_debug [ STR "Unexpected value in dehex_string: " ; INT ich ; NL ] ;
          raise (CCFailure (LBLOCK [ STR "Unexpected value in dehex_string: " ; INT ich ]))
        end
      else
        s := !s ^ (String.make 1 (Char.chr ich))
    done ;
    !s
  end
    
let has_control_characters s =
  let found = ref false in
  let _ =
    String.iter (fun c ->
        let code = Char.code c in
        if (code < 32)  || (code > 126) then
          found := true) s in
  !found

let encode_string (s:string) =
  if has_control_characters s then
    (true, hex_string s)
  else 
    (false, s)

let decode_string (e:(bool * string)) =
  let (ishex,s) = e in
  if ishex then
    dehex_string s
  else
    s
  
class string_index_table_t (name:string):string_index_table_int =
object (self)

  val mutable next = 1
  val table = H.create 3        (* string -> index *)
  val revtable = H.create 3     (* index -> string *)

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
       raise (CCFailure (LBLOCK [ STR "Index " ; INT index ; STR " not found in string table" ]))

  method values = H.fold (fun k _ r -> k :: r) table []

  method items = H.fold (fun k index r -> (k,index) :: r) table []

  method private get_indexed_keys =
    List.sort P.compare (H.fold (fun k v r -> (k,v) :: r) revtable [])               

  method size = H.length table

  method read_xml (node:xml_element_int) =
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
        end) (node#getTaggedChildren "n")

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

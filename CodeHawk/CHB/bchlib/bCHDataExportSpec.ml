(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

module H = Hashtbl


let read_xml_data_export_spec_item (node:xml_element_int) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  { dex_offset = geti "offset" ;
    dex_name = if has "name" then get "name" else ("item-" ^ (get "offset")) ;
    dex_type = get "type" ;
    dex_size = geti "size"
  }

let read_xml_data_export_spec (node:xml_element_int) =
  let get = node#getAttribute in
  let getcc = node#getTaggedChildren in
  { dex_description = get "desc" ;
    dex_items = List.map read_xml_data_export_spec_item (getcc "ex-item")
  }

let get_spec_size (spec:data_export_spec_t) =
  let (maxOffset,size) = List.fold_left (fun (m,s) i ->
    if i.dex_offset > m then (i.dex_offset,i.dex_size) else (m,s)) (0,0) spec.dex_items in
  maxOffset + size

let data_export_spec_to_pretty (spec:data_export_spec_t) =
    let frp p s = fixed_length_pretty ~alignment:StrRight p s in
    let flp p s = fixed_length_pretty p s in
    let item_to_pretty i =
      LBLOCK [ frp (INT i.dex_offset) 5 ; STR "  " ;
	       flp (STR i.dex_name) 10 ; STR "  " ;
	       flp (STR i.dex_type) 10 ; NL ] in
    LBLOCK [ STR spec.dex_description ; NL ;
	     INDENT ( 3, LBLOCK (List.map item_to_pretty spec.dex_items) ) ; NL ]

let extract_export_spec_values (spec:data_export_spec_t) (ch:pushback_stream_int) =
  let items =
    List.sort (fun i1 i2 -> Stdlib.compare i1.dex_offset i2.dex_offset) spec.dex_items in
  let result = ref [] in
  begin
    List.iter (fun item ->
      let _ = if ch#pos < item.dex_offset then ch#skip_bytes (item.dex_offset - ch#pos) in
      let _ =
        if ch#pos > item.dex_offset then
	  raise (BCH_failure
                   (LBLOCK [ STR "Error in reading export values: " ; 
			     STR "current position: " ; INT ch#pos ;
			     STR "; expected offset: " ; INT item.dex_offset ])) in
      let v = match (item.dex_type,item.dex_size) with
	| ("unknown",4) -> ch#read_doubleword
	| ("string",4) -> ch#read_doubleword
	| ("function-pointer",4) -> ch#read_doubleword
	| ("int",4) -> ch#read_doubleword
	| (ty,si) ->
           raise (BCH_failure
                    (LBLOCK [ STR "Export spec item not supported: " ;
			      STR "type: " ; STR ty ; 
			      STR "; size: " ; INT si ])) in
      result  := (item.dex_offset, v) :: !result) items ;
    !result
  end

class data_export_value_t 
  (spec:data_export_spec_t) 
  (addr:doubleword_int):data_export_value_int =
object

  val values = H.create 3

  method set_values (l:(int * string) list) =
    List.iter (fun (i,v) -> H.add values i v) l

  method get_spec = spec

  method get_size = get_spec_size spec

  method get_values = 
    List.map (fun i ->
      try
	(i, H.find values i.dex_offset)
      with
	Not_found ->
	raise (BCH_failure
                 (LBLOCK [ STR "Incomplete data export values for " ; 
			   STR spec.dex_description ; 
			   STR "; item at offset " ; INT i.dex_offset ;
			   STR " is missing" ])))
      spec.dex_items

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let append = node#appendChildren in
    begin
      append (List.map (fun item ->
	let iNode = xmlElement "exitem" in
	let set = iNode#setAttribute in
	let seti = iNode#setIntAttribute in
	begin
	  seti "offset" item.dex_offset ;
	  set "name" item.dex_name ;
	  set "type" item.dex_type ;
	  seti "size" item.dex_size ;
	  set "value" (H.find values item.dex_offset) ;
	  iNode
	end) spec.dex_items) ;
      set "desc" spec.dex_description ;
      set "addr" addr#to_hex_string
    end

  method toPretty =
    let frp p s = fixed_length_pretty ~alignment:StrRight p s in
    let flp p s = fixed_length_pretty p s in
    let item_to_pretty i =
      LBLOCK [ frp (INT i.dex_offset) 5 ; STR "  " ;
	       flp (STR i.dex_name) 10 ; STR "  " ;
	       flp (STR i.dex_type) 10 ; STR "  " ;
	       STR (H.find values i.dex_offset) ; NL ] in
    LBLOCK [ STR spec.dex_description ; NL ;
	     INDENT ( 3, LBLOCK (List.map item_to_pretty spec.dex_items) ) ; NL ]

end


let make_data_export_value (spec:data_export_spec_t) (addr:doubleword_int)
    (values:(int * string) list) =
  let v = new data_export_value_t spec addr in
  let _ = v#set_values values in
  v

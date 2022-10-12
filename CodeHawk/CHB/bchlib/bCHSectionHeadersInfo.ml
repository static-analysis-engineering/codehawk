(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2021      Henny Sipma
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

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHXmlUtil

module H = Hashtbl


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


let valid_fields =
  ["addr"; "addralign"; "entsize"; "flags"; "info"; "link"; "offset"; "size"; "type"]


class section_header_info_t (sectionname:string):section_header_info_int =
object (self)

  val fields = H.create 3

  method get_name = sectionname

  method has_addr = H.mem fields "addr"
  method has_size = H.mem fields "size"
  method has_offset = H.mem fields "offset"
  method has_type = H.mem fields "type"
  method has_link = H.mem fields "link"
  method has_info = H.mem fields "info"
  method has_flags = H.mem fields "flags"
  method has_addralign = H.mem fields "addralign"
  method has_entsize = H.mem fields "entsize"

  method private get_field (name:string) =
    if H.mem fields name then
      H.find fields name
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Section header info for ";
                STR sectionname;
                STR " does not have a ";
                STR name;
                STR " field" ]))

  method get_addr = self#get_field "addr"
  method get_size = self#get_field "size"
  method get_offset = self#get_field "offset"
  method get_flags = self#get_field "flags"
  method get_type = self#get_field "type"
  method get_link = self#get_field "link"
  method get_info = self#get_field "info"
  method get_addralign = self#get_field "addralign"
  method get_entsize = self#get_field "entsize"

  method read_xml (node:xml_element_int) =
    begin
      List.iter (fun n -> 
          let get = n#getAttribute in
          let geta tag =
            try
              string_to_doubleword (get tag)
            with
            | BCH_failure p ->
               raise_xml_error node (LBLOCK [STR "section header info: "; p]) in
          let fldname = get "name" in
          if List.mem fldname valid_fields then
            let fldvalue = geta "value" in
            H.add fields fldname fldvalue
          else
            let msg =
              LBLOCK [
                  STR "Field name ";
                  STR fldname;
                  STR " not recognized for section header "] in
            raise_xml_error n msg) (node#getTaggedChildren "fld");
      chlog#add
        "section header info"
        (let flds = H.fold (fun k _ a -> k::a) fields [] in
         LBLOCK [
             STR sectionname;
             STR " fields: ";
             pretty_print_list flds (fun f -> STR f) "[" ", " "]" ])
    end

  method toPretty =
    let fields =
      List.map
        (fun (k,v) -> LBLOCK [STR k; STR ": "; v#toPretty; NL])
        (H.fold (fun k v a -> (k,v)::a) fields []) in
    LBLOCK [STR "Section header "; STR sectionname; NL; LBLOCK fields]
end


class section_header_infos_t: section_header_infos_int =
object (self)

  val sectionheaders = H.create 3 (* section name -> section_header_info *)

  method has_section_header_info (name: string) = H.mem sectionheaders name

  method has_section_header_infos = (H.length sectionheaders) > 0

  method get_section_header_info (name: string) =
    if self#has_section_header_info name then
      H.find sectionheaders name
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Section header info for ";
                STR name;
                STR " not found"]))

  method get_section_header_names = H.fold (fun k _ a -> k::a) sectionheaders []

  method private read_xml_section_header_info (node: xml_element_int) =
    let name = node#getAttribute "name" in
    let shinfo = new section_header_info_t name in
    begin
      shinfo#read_xml node ;
      H.add sectionheaders name shinfo
    end

  method read_xml (node:xml_element_int) =
    List.iter self#read_xml_section_header_info (node#getTaggedChildren "sh")

  method toPretty =
    LBLOCK
      (List.map (fun v -> LBLOCK  [v#toPretty; NL])
         (H.fold (fun _ v a -> v::a) sectionheaders []))

end


let section_header_infos = new section_header_infos_t

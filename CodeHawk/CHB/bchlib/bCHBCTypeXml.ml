(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open BCHBCSumTypeSerializer
open BCHBCTypes
open BCHBCTypeUtil


let raise_error (node: xml_element_int) (msg: pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


let read_xml_summary_type (node: xml_element_int): btype_t =
  let rec aux n =
    if n#hasText then 
      TNamed (n#getText,[])
    else
      let nn = n#getChild in
      match nn#getTag with
      | "float" -> t_float
      | "ptr" -> TPtr (aux nn,[])
      | "array" -> 
	 let size =
           if nn#hasNamedAttribute "size" then
	     Some
               (Const
                  (CInt (Int64.of_string (nn#getAttribute "size"), IInt, None)))
	  else
	    None in
	TArray (aux nn, size,[])
      | "vararg" -> TVarArg []
      | "struct" -> t_named (nn#getAttribute "name")
      | s ->
	raise_error node 
	  (LBLOCK [ STR s ; STR " not recognized as a summary type" ]) in
  aux node


let compinfo_key = ref 10000
let new_compinfo_key () =
  begin
    compinfo_key := !compinfo_key + 1;
    !compinfo_key
  end


let read_xml_summary_fieldinfo
      (ckey: int) (node: xml_element_int) : bfieldinfo_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let geti = node#getIntAttribute in
  let tNode = getc "type" in
  {
    bfckey = ckey;
    bfname = get "name";
    bftype = read_xml_summary_type tNode;
    bfbitfield = None;
    bfattr = [];
    bfloc = {line = 0; file = ""; byte = 0};
    bfieldlayout =
      if has "offset" && has "size" then
        Some (geti "offset", geti "size")
      else
        None
  }


let read_xml_summary_struct (node: xml_element_int): bcompinfo_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let ckey = new_compinfo_key () in
  {
    bcname = get "name";
    bckey = ckey;
    bcstruct = true;
    bcfields =
      List.map
        (read_xml_summary_fieldinfo ckey)
        ((getc "fields")#getTaggedChildren "field");
    bcattr = []
  }


let read_xml_int64 (node: xml_element_int): int64 =
  Int64.of_string (node#getAttribute "intValue")


let write_xml_int64_element (node: xml_element_int) (i :int64) =
  node#setAttribute "intValue" (Int64.to_string i)


let read_xml_int64_list (node: xml_element_int): int64 list =
  List.map read_xml_int64 (node#getTaggedChildren "int")


let write_xml_int64_list (node: xml_element_int) (l: int64 list) =
  node#appendChildren
    (List.map (fun i ->
         let inode = xmlElement "int" in
         begin write_xml_int64_element inode i; inode end) l)


let read_xml_restricted_btype (node: xml_element_int): btype_t =
  let get = node#getAttribute in
  match get "ttag" with
  | "tvoid" -> TVoid []
  | "tint" -> TInt (ikind_mfts#fs (get "ikind"), [])
  | "tnamed" -> TNamed (get "tname", [])
  | s -> raise_error node (LBLOCK [STR s; STR " no recognized as type tag"])


let read_xml_type (node: xml_element_int) =
  if node#getTag = "btype" || node#getTag = "typ" then 
    read_xml_restricted_btype node 
  else 
    read_xml_summary_type node


and read_xml_returntype (node: xml_element_int) =
  if node#getTag = "returnbtype" then
    read_xml_restricted_btype node
  else
    read_xml_summary_type node


let get_standard_char_type_replacements (char_type: string) =
  if char_type = "ansi" || char_type = "A" then
    [ ("LPCTSTR", "LPCSTR");
      ("LPTSTR", "LPSTR");
      ("TCHAR", "char")]
  else if char_type = "unicode" || char_type = "W" then
    [ ("LPCTSTR", "LPCWSTR");
      ("LPTSTR", "LPWSTR");
      ("TCHAR", "wchar_t")]
  else
    raise (BCH_failure
             (LBLOCK [
                  STR char_type;
		  STR " is not a valid ansi/unicode designation. ";
		  STR "Use A/W or ansi/unicode"]))


let read_xml_type_transformer (node: xml_element_int) =
  let get = node#getAttribute in
  let getcc = node#getTaggedChildren in
  let has = node#hasNamedAttribute in
  let replacements = List.map (fun n ->
    let get = n#getAttribute in (get "src", get "tgt")) (getcc "replace-type") in
  let replacements = if has "char-type" then 
      (get_standard_char_type_replacements (get "char-type")) @ replacements
    else
      replacements in
  let replace s = 
    try let (_,t) = List.find (fun (x,_) -> x = s) replacements in t with 
      Not_found -> s in
  replace
       

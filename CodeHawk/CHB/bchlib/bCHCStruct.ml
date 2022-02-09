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
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* bchcil *)
open BCHCBasicTypes

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHPreFileIO
open BCHTypeDefinitions
open BCHVariableType
open BCHXmlUtil

module H = Hashtbl


class c_struct_t (name: string) (fields:struct_field_t list) =
object

  val table = 
    let t = H.create 3 in
    let _ = List.iter (fun f -> H.add t f.fld_offset f) fields in
    t

  method get_name = name 

  method get_field (offset:int) =
    if H.mem table offset then H.find table offset else
      raise
        (BCH_failure
           (LBLOCK [STR "No field found at offset "; INT offset]))

  method has_field (offset:int) = H.mem table offset

  method iter (f:(struct_field_t -> unit)) = H.iter (fun _ v -> f v) table

  method toPretty =
    let pr p n = fixed_length_pretty ~alignment:StrRight p n in
    LBLOCK [
        STR "struct ";
        STR name;
        NL;
	LBLOCK
          (List.map (fun f ->
	       INDENT
                 (3, LBLOCK [
                         pr (INT f.fld_offset) 5;
                         STR "  ";
			 btype_to_pretty f.fld_type;
                         STR " ";
			 STR f.fld_name; NL])) fields);
        NL;
        STR "end";
        NL]
				   

end

let read_xml_field (node:xml_element_int) =
  let getc = node#getTaggedChild in
  let get = node#getAttribute in 
  let geti = node#getIntAttribute in {
    fld_name = get "name" ;
    fld_offset = geti "offset" ;
    fld_size = geti "size" ;
    fld_type = read_xml_type (getc "type")
  }				  

let read_xml_c_struct (name:string) (node:xml_element_int) =
  try
    let getcc = (node#getTaggedChild "fields")#getTaggedChildren in
    let name = node#getAttribute "name" in
    let fields = List.map read_xml_field (getcc "field") in
    new c_struct_t name fields
  with
  | XmlParseError (line, col, p)
    | XmlReaderError (line, col, p)
    | XmlDocumentError (line, col, p) ->
     let msg = LBLOCK [ STR "Xml error in "; STR name; STR ": "; p] in
     begin
       ch_error_log#add "xml error" msg;
       raise (XmlDocumentError (line,col,msg))
     end

let cstructs = H.create 3

let add_user_c_struct (name:string) =
  if H.mem cstructs name then
    ()
  else
    match load_userdata_struct_file name with
    | Some node ->
      let s = read_xml_c_struct name node in
      begin
	H.add cstructs s#get_name s ;
	chlog#add "user struct" (LBLOCK [STR s#get_name])
      end
    | _ -> 
       raise
         (BCH_failure
            (LBLOCK [STR "No struct file found for "; STR name]))


let add_library_struct (node:xml_element_int) =
  let s = read_xml_c_struct "library struct" node in
  begin
    H.add cstructs s#get_name s ;
    chlog#add "library struct" (LBLOCK [ STR s#get_name ])
  end

let get_c_struct (name:string) =
  try
    H.find cstructs name 
  with
  | Not_found ->
     raise
       (BCH_failure (LBLOCK [STR "Struct " ;STR name; STR " not found"]))

let get_pointedto_struct (ty:btype_t) =
  match ty with
  | TPtr (TNamed (name,_),_) -> get_c_struct name
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Type is not a pointer to a struct: ";
	       btype_to_pretty ty]))

let get_struct (ty:btype_t) =
  match ty with
  | TNamed (name,_) -> get_c_struct name
  | _ ->
     raise
       (BCH_failure
	  (LBLOCK [
               STR "Type is not a known struct: "; btype_to_pretty ty]))

let is_ptrto_known_struct (ty:btype_t) =
  match ty with
  | TPtr (TNamed (name,_),_) -> H.mem cstructs name
  | _ -> false

let is_known_struct (ty:btype_t) =
  match ty with
  | TNamed (name,_) -> H.mem cstructs name
  | _ -> false


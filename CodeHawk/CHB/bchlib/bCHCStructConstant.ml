(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHDoubleword
open BCHLibTypes
open BCHUtilities
open BCHXmlUtil

module H = Hashtbl
module P = Pervasives


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
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


(* --------------------------------------------------------------- repository *)

let table = H.create 3

let add_structconstant (name:string) (sc:c_struct_constant_t) = 
  H.replace table name sc

let has_structconstant (name:string) = H.mem table name

let get_structconstant (name:string) =
  if H.mem table name then
    H.find table name
  else
    raise (BCH_failure
             (LBLOCK [
                  STR "C struct constant ";
                  STR name ; STR " not found"]))


(* ----------------------------------------------------------------- printing *)

let cstructconstant_to_pretty (sc:c_struct_constant_t) =
  let rec aux sc indent =
    match sc with
    | FieldCallTarget tgt -> call_target_to_pretty tgt
    | FieldConstant t -> bterm_to_pretty t
    | FieldString s -> STR s
    | FieldValues sscs ->
      let pFields =
	LBLOCK
          (List.map (fun (offset,ssc) ->
	       (LBLOCK [
                    INDENT(
                        indent,
			LBLOCK [
                            fixed_length_pretty
                              ~alignment:StrRight (INT offset) 5;
			    STR "  ";
                            aux ssc (indent + 3);
                            NL])])) sscs) in
      LBLOCK [STR "function table"; NL; pFields] in
  aux sc 0

(* --------------------------------------------------------------- comparison *)

let rec cstructconstant_compare sc1 sc2 =
  match (sc1,sc2) with
  | (FieldValues ssc1,FieldValues ssc2) ->
     list_compare ssc1 ssc2 fieldvalue_compare
  | (FieldValues _, _) -> -1
  | (_, FieldValues _) -> 1
  | (FieldConstant t1, FieldConstant t2) -> bterm_compare t1 t2
  | (FieldConstant _, _) -> -1
  | (_, FieldConstant _) -> 1
  | (FieldString s1, FieldString s2) -> P.compare s1 s2
  | (FieldString _, _) -> -1
  | (_, FieldString _) -> 1
  | (FieldCallTarget tgt1, FieldCallTarget tgt2) ->
     call_target_compare tgt1 tgt2

and fieldvalue_compare fv1 fv2 =
  match (fv1,fv2) with
  | ((o1,sc1), (o2,sc2)) ->
    let l1 = P.compare o1 o2 in
    if l1 = 0 then cstructconstant_compare sc1 sc2 else l1


(* ----------------------------------------------------------------- read xml *)

let read_xml_cstructconstant (node:xml_element_int):c_struct_constant_t =
  let rec aux node =
    let fieldvalues = List.map (fun n ->
      let get = n#getAttribute in
      let geti = n#getIntAttribute in
      let geta () = string_to_doubleword (get "a") in
      let has = n#hasNamedAttribute in
      let offset = n#getIntAttribute "offset" in
      let sc = match n#getAttribute "tag" with
	| "dll" ->
           FieldCallTarget(StubTarget(DllFunction (get "dll", get "name")))
	| "app" -> FieldCallTarget(AppTarget(geta ()))
	| "struct" -> 
	  if has "name" then 
	    let name = get "name" in
	    if has_structconstant name then
		get_structconstant name 
	    else
	      raise
                (BCH_failure
                   (LBLOCK [
                        STR "Struct constant ";
                        STR name;
			STR " not found"]))
	  else
	    aux (n#getTaggedChild "field-values")
	| "cn" -> FieldConstant (NumConstant (mkNumerical (geti "value")))
	| "string" -> FieldString (get "str")
	| s ->
           raise_xml_error
             n
	     (LBLOCK [
                  STR "c struct constant tag ";
                  STR s;
                  STR " not recognized"]) in
      (offset, sc)) (node#getTaggedChildren "fv") in
    FieldValues fieldvalues in
  aux (node#getTaggedChild "field-values")



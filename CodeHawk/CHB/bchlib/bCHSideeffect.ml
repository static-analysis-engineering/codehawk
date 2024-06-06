(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHBCTypeXml
open BCHBTerm
open BCHFtsParameter
open BCHLibTypes
open BCHPrecondition
open BCHTypeDefinitions


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
    ch_error_log#add "xml parse error" error_msg;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

(* ----------------------------------------------------------------- read xml *)

let read_xml_par_sideeffects
      (node:xml_element_int) (_thisf: bterm_t): xxpredicate_t list =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let one = IndexSize (NumConstant numerical_one) in
  let getsize n =
    let has = n#hasNamedAttribute in
    let geti = n#getIntAttribute in
    if has "bytesize" then
      ByteSize (NumConstant (mkNumerical (geti "bytesize")))
    else if has "indexsize" then
      IndexSize (NumConstant (mkNumerical (geti "indexsize")))
    else
      one in
  let sNodes =
    if hasc "sideeffects" then
      (getc "sideeffects")#getChildren
    else
      [] in
  let par = read_xml_fts_parameter node in
  let t = ArgValue par in
  let ty () =
    let t = match BCHTypeDefinitions.resolve_type par.apar_type with
      | TFun _ -> par.apar_type
      | TPtr (t,_) -> t
      | THandle (s,_) -> TNamed (s,[])
      | _ ->
	raise_xml_error node
	  (LBLOCK [
               STR "Expected pointer type for ";
               STR par.apar_name;
	       STR ", but found ";
               btype_to_pretty par.apar_type]) in
    match t with
    | TNamed (name,_) when type_definitions#has_type name ->
       type_definitions#get_type name
    | _ -> t in
  let aux node =
    match node#getTag with
    | "block-write" -> XXBlockWrite (ty (), t, getsize node)
    | "block-write-null" ->
      XXConditional (XXNotNull t, XXBlockWrite (ty (), t, getsize node))
    | "invalidates" -> XXInvalidated t
    | "modifies" -> XXModified t
    | s ->
       raise_xml_error
         node
         (LBLOCK [
              STR "Parameter side effect ";
              STR s;
              STR " not recognized"]) in
  List.map aux sNodes


let read_xml_sideeffect
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t =
  let get_term n = read_xml_bterm n thisf parameters in
  let get_type n =
    let t = read_xml_type n in
    match t with
    | TNamed (name,_) when type_definitions#has_type name ->
       type_definitions#get_type name
    | _ -> t in
  let rec aux node =
    let cNodes = node#getChildren in
    let pNode = List.hd cNodes in
    let argNodes = List.tl cNodes in
    let arg n =
      try List.nth argNodes n with Failure _ ->
        raise_xml_error
          node
          (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    match pNode#getTag with
    | "block-write" ->
      XXBlockWrite (get_type (arg 0), get_term (arg 1), get_term (arg 2))
    (* | "allocates-stack-memory" -> AllocatesStackMemory (get_term (arg 0)) *)
    | "modifies" -> XXModified (get_term (arg 0))
    | "starts-thread" ->
      XXStartsThread (get_term (arg 0), List.map get_term (List.tl argNodes))
    | "invalidates" -> XXInvalidated (get_term (arg 0))
    | "sets-errno" -> XXSetsErrno
    | "implies" ->
       let condition =
         List.hd
           (read_xml_precondition_xxpredicate
	      ((node#getTaggedChild "pre")#getTaggedChild "apply")
              thisf
              parameters) in
       XXConditional (condition, aux (node#getTaggedChild "apply"))
    | s ->
       raise_xml_error
         node
         (LBLOCK [
              STR "Sideeffect predicate ";
              STR s;
              STR " not recognized"]) in
  match (node#getTaggedChild "math")#getChild#getTag with
  | "sets-errno" -> XXSetsErrno
  (* | "unknown-sideeffect" -> UnknownSideeffect *)
  | _ -> aux ((node#getTaggedChild "math")#getTaggedChild "apply")


let read_xml_sideeffects
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n -> read_xml_sideeffect n thisf parameters) (getcc "sideeffect")


let make_attribute_sideeffects
      (attrs: precondition_attribute_t list)
      (parameters: fts_parameter_t list): xxpredicate_t list =
  let get_par (n: int) =
    try
      List.find (fun p ->
          match p.apar_index with Some ix -> ix = n | _ -> false) parameters
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "No parameter with index ";
                 INT n;
	         pretty_print_list (List.map (fun p -> p.apar_name) parameters)
	           (fun s -> STR s) "[" "," "]" ])) in
  let get_derefty (par: fts_parameter_t): btype_t =
    if is_pointer par.apar_type then
      ptr_deref par.apar_type
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "parameter is not a pointer type: ";
                fts_parameter_to_pretty par])) in
  List.fold_left (fun acc attr ->
      match attr with
      | (APCWriteOnly (n, None)) ->
         let par = get_par n in
         let ty = get_derefty par in
         (XXBlockWrite (ty, ArgValue par, RunTimeValue)) :: acc
      | _ -> acc) [] attrs

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open XprTypes
open XprToPretty

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeTransformer
open BCHBCTypeXml
open BCHBTerm
open BCHCStructConstant
open BCHExternalPredicate
open BCHLibTypes
open BCHTypeDefinitions
open BCHUtilities
open BCHXmlUtil


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

let read_xml_par_preconditions
      (node:xml_element_int) (thisf: bterm_t): xxpredicate_t list =
  let one = IndexSize (NumConstant numerical_one) in
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let pNodes = if hasc "pre" then (getc "pre")#getChildren else [] in
  let par = read_xml_fts_parameter node in
  let t = ArgValue par in
  let ty () = match BCHTypeDefinitions.resolve_type par.apar_type with
    | TFun _ -> par.apar_type
    | TPtr (t, _) -> t
    | THandle (s, _) -> TNamed (s, [])
    | _ ->
      raise_xml_error node
	(LBLOCK [
             STR "Pre: Expected pointer type for ";
             STR par.apar_name;
	     STR ", but found ";
             btype_to_pretty par.apar_type]) in
  let getsize n typ =
    let has = n#hasNamedAttribute in
    let geti = n#getIntAttribute in
    if has "bytesize" then
      ByteSize (NumConstant (mkNumerical (geti "bytesize")))
    else if has "indexsize" then
      IndexSize (NumConstant (mkNumerical (geti "indexsize")))
    else match get_size_of_type typ with
    | Some i -> NumConstant (mkNumerical i)
    | _ -> one in
  let aux node =
    match node#getTag with
    | "null-terminated" -> [XXNullTerminated t]
    | "not-null" -> [XXNotNull t]
    | "null" -> [XXNull t]
    | "deref-read" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ);
        XXInitializedRange (typ, t, getsize node typ);
        XXNotNull t;]
    | "deref-read-nt" ->
       let typ = ty () in
       [XXBuffer (typ, t, ArgNullTerminatorPos t);
        XXInitializedRange (typ, t, ArgNullTerminatorPos t);
        XXNotNull t;
        XXNullTerminated t]
    | "deref-read-null" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ);
        XXInitializedRange (typ, t, ArgNullTerminatorPos t)]
    | "deref-read-null-nt" ->
       let typ = ty () in
       [XXBuffer (typ, t, ArgNullTerminatorPos t);
        XXInitializedRange (typ, t, ArgNullTerminatorPos t);
        XXNullTerminated t]
    | "deref-write" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ); XXNotNull t]
    | "deref-write-null" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ)]
    | "allocation-base" -> [XXAllocationBase t]
    | "function-pointer" ->
       let typ = ty () in [XXFunctionPointer (typ, t)]
    | "format-string" -> [XXOutputFormatString t]
    | "includes" ->
      let name = node#getAttribute "name" in
      [XXIncludes (t,get_structconstant name)]
    | "enum-value" ->
       let flags =
         node#hasNamedAttribute "flags"
         && (node#getAttribute "flags") = "true" in
       [XXEnum (t, node#getAttribute "name", flags)]
    | "non-negative"
      | "nonnegative" -> [XXNonNegative t]
    | "positive" -> [XXPositive t]
    | s ->
       raise_xml_error node
         (LBLOCK [
              STR "Parameter precondition ";
              STR s;
              STR " not recognized"]) in
  List.concat (List.map aux pNodes)


let read_xml_precondition_xxpredicate
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t list =
  let gt n = read_xml_bterm n thisf parameters in
  let gty = read_xml_type in
  let rec aux node =
    let cNodes = node#getChildren in
    let pNode = List.hd cNodes in
    let argNodes = List.tl cNodes in
    let arg n =
      try
        List.nth argNodes n
      with
      | Failure _ ->
         raise_xml_error
           node
           (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    if is_relational_operator pNode#getTag then
      let op = get_relational_operator pNode#getTag in
      [XXRelationalExpr (op, gt (arg 0), gt (arg 1))]
    else
      match pNode#getTag with
      | "or" -> [XXDisjunction (List.concat (List.map aux argNodes))]
      | "implies" ->
         [XXConditional (List.hd (aux (arg 0)), List.hd (aux (arg 1)))]
      | "not-null" -> [XXNotNull (gt (arg 0))]
      | "null" -> [XXNull (gt (arg 0))]
      | "null-terminated" -> [XXNullTerminated (gt (arg 0))]
      | "format-string" -> [XXOutputFormatString (gt (arg 0))]
      | "allocation-base" -> [XXAllocationBase (gt (arg 0))]
      | "function-pointer" -> [XXFunctionPointer (gty(arg 0), gt (arg 1))]
      | "enum-value" ->
	let flags =
	  (pNode#hasNamedAttribute "flags")
          && (pNode#getAttribute "flags") = "true" in
	[XXEnum (gt (arg 0), pNode#getAttribute "name", flags)]
      | "includes" ->
	let sc = read_xml_cstructconstant (pNode#getTaggedChild "sc") in
	[XXIncludes (gt (arg 0), sc)]
      | "deref-read" | "block-read" ->
	 [XXBuffer (gty (arg 0), gt (arg 1), gt (arg 2));
          XXNotNull (gt (arg 1))]
      | "deref-read-null" -> [XXBuffer (gty (arg 0), gt (arg 1), gt (arg 2))]
      | "deref-read-nt" ->
	let dest = gt (arg 1) in
	let len = ArgNullTerminatorPos dest in
	[XXBuffer (gty (arg 0), dest, len); XXNotNull dest]
      | "deref-read-nt-null" ->
	let dest = gt (arg 1) in
	let len = ArgNullTerminatorPos dest in
	[XXBuffer (gty (arg 0), dest, len)]
      | "deref-write" ->
         let dest = gt (arg 1) in
	 [XXBlockWrite (gty (arg 0), dest, gt (arg 2)); XXNotNull dest]
      | "deref-write-null" ->
	[XXBlockWrite (gty (arg 0), gt (arg 1), gt (arg 2))]
      | s ->
         raise_xml_error
           node
	   (LBLOCK [
                STR "Precondition predicate symbol ";
                STR s;
                STR " not recognized"]) in
  aux node


let read_xml_precondition
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t list =
  read_xml_precondition_xxpredicate
    ((node#getTaggedChild "math")#getTaggedChild "apply") thisf parameters


let read_xml_preconditions
      (node:xml_element_int)
      (thisf: bterm_t)
      (parameters: fts_parameter_t list): xxpredicate_t list =
  let getcc = node#getTaggedChildren in
  List.concat
    (List.map
       (fun n ->
         read_xml_precondition n thisf parameters) (getcc "pre"))

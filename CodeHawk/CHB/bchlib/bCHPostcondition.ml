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
open BCHBCTypeXml
open BCHBTerm
open BCHExternalPredicate
open BCHLibTypes
open BCHPrecondition


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

let read_xml_postcondition
      (node: xml_element_int)
      (thisf: bterm_t)
      (parameters: fts_parameter_t list): xxpredicate_t =
  let get_term n = read_xml_bterm n thisf parameters in
  let rec aux node =
    let cNodes = node#getChildren in
    let pNode = List.hd cNodes in
    let argNodes = List.tl cNodes in
    let arg n =
      try List.nth argNodes n with Failure _ ->
        raise_xml_error
          node
          (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    if is_relational_operator pNode#getTag then
      let op = get_relational_operator pNode#getTag in
      XXRelationalExpr (op, get_term (arg 0), get_term (arg 1))
    else
      match pNode#getTag with
      | "new-memory-region" ->
         XXNewMemory (get_term (arg 0), get_term (arg 1))
      | "function-pointer" ->
         XXFunctionPointer (read_xml_type (arg 0), get_term (arg 1))
      | "allocation-base" -> XXAllocationBase (get_term (arg 0))
      | "null" -> XXNull (get_term (arg 0))
      | "not-null" -> XXNotNull (get_term (arg 0))
      | "null-terminated" -> XXNullTerminated (get_term (arg 0))
      | "enum" -> XXEnum (get_term (arg 0), pNode#getAttribute "name", false)
      | "non-returning" -> XXFalse
      | "or" -> XXDisjunction (List.map aux pNode#getChildren)
      | "implies" ->
         let condition =
	   List.hd
             (read_xml_precondition_xxpredicate
	        ((pNode#getTaggedChild "pre")#getTaggedChild "apply")
                thisf
                parameters) in
         XXConditional
           (condition, aux (pNode#getTaggedChild "apply"))
      | s ->
         raise_xml_error
           node
	   (LBLOCK [
                STR "Postcondition predicate ";
                STR s;
                STR " not recognized"]) in
  match (node#getTaggedChild "math")#getChild#getTag with
  | "non-returning" -> XXFalse
  | _ -> aux ((node#getTaggedChild "math")#getTaggedChild "apply")


let read_xml_postconditions
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n -> read_xml_postcondition n thisf parameters) (getcc "post")


let read_xml_errorpostconditions
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n ->
      read_xml_postcondition n thisf parameters) (getcc "error-post")


let read_xml_shortcut_postconditions
      (node:xml_element_int)
      (thisf: bterm_t): xxpredicate_t list * xxpredicate_t list =
  let zero = NumConstant numerical_zero in
  let rv = ReturnValue thisf in
  List.fold_left (fun (p, ep) n ->
    match n#getTag with
    | "post" | "error-post" -> (p, ep)
    | "enum" -> ((XXEnum (rv, n#getAttribute "name", false)):: p, ep)
    | "non-returning" -> (XXFalse :: p, ep)
    | "null-terminated" -> ((XXNullTerminated rv) :: p, ep)
    | "notzero-zero" | "nonzero-zero" ->
      ((XXRelationalExpr (PNotEqual, rv, zero)) :: p,
       (XXRelationalExpr (PEquals, rv, zero)) :: ep)
    | "zero-nonzero" | "zero-notzero" ->
      ((XXRelationalExpr (PEquals, rv, zero)) :: p,
       (XXRelationalExpr (PNotEqual, rv, zero)) :: ep)
    | "zero-negone" ->
      let negone = NumConstant (mkNumerical (-1)) in
      ((XXRelationalExpr (PEquals, rv, zero)) :: p,
       (XXRelationalExpr (PEquals, rv, negone) ) :: ep)
    | "zero-negative" ->
      ((XXRelationalExpr (PEquals, rv, zero)) :: p,
       (XXRelationalExpr (PLessThan, rv, zero)) :: ep)
    | "one-zero" ->
      let one = NumConstant numerical_one in
      ((XXRelationalExpr (PEquals, rv, one)) :: p,
       (XXRelationalExpr (PEquals, rv, zero) ) :: ep)
    | "notnull" -> ((XXNotNull rv):: p, ep)
    | "notnull-null" ->
      ((XXNotNull rv):: p, (XXNull rv) :: ep)
    | "null-notnull" ->
      ((XXNull rv) :: p, (XXNotNull rv ) :: ep)
    | "nonnegative-negone" ->
      let negone = NumConstant (mkNumerical (-1)) in
      ((XXRelationalExpr (PGreaterEqual, rv, zero)) :: p,
       (XXRelationalExpr (PEquals, rv, negone)) :: ep)
    | "nonnegative-negative" ->
      ((XXRelationalExpr (PGreaterEqual, rv, zero)) :: p,
       (XXRelationalExpr (PLessThan, rv, zero)) :: ep)
    | "positive-nonpositive" ->
      ((XXRelationalExpr (PGreaterThan, rv, zero)) :: p,
       (XXRelationalExpr (PLessEqual, rv, zero)) :: ep)
    | "positive-zero" ->
      ((XXRelationalExpr (PGreaterThan, rv, zero)) :: p,
       (XXRelationalExpr (PEquals, rv, zero)) :: ep)
    | s -> raise_xml_error n
      (LBLOCK [STR s; STR " not recognized as a shortcut postcondition"]))
    ([],[]) node#getChildren

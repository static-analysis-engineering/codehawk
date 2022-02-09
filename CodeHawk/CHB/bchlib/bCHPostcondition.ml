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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt

(* bchcil *)
open BCHCBasicTypes

(* bchlib *)
open BCHBasicTypes
open BCHBTerm
open BCHLibTypes
open BCHPrecondition
open BCHXmlUtil


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


(* ----------------------------------------------------------------- printing *)

let postcondition_to_pretty (predicate:postcondition_t) =
  let default name terms =
    LBLOCK [STR name; pretty_print_list terms bterm_to_pretty "(" ", " ")"] in
  let rec toPretty pred =
    match pred with
    | PostNewMemoryRegion (t1,t2) -> default "new-memory-region" [t1; t2]
    | PostFunctionPointer (t1,t2) -> default "post-function-pointer" [t1; t2]
    | PostAllocationBase t -> default "allocation-base" [t]
    | PostNull t -> default "null" [t]
    | PostNotNull t -> default "not-null" [t]
    | PostEnum (t,name) ->
      LBLOCK [ STR "enum ("; bterm_to_pretty t; STR ","; STR name; STR ")"]
    | PostFalse  -> LBLOCK [ STR "non-returning" ]
    | PostNullTerminated t -> default "null-terminated" [t]
    | PostRelationalExpr (op,x,y) ->
       LBLOCK [
           bterm_to_pretty x;
           STR (relational_op_to_string op);
	   bterm_to_pretty y]
    | PostDisjunction predicateList ->
      let (_,pp) = List.fold_left
	(fun (first,acc) p ->
	  (false,
           LBLOCK [
               acc;
               (if first then STR "" else LBLOCK [STR " or "; NL]);
	       (INDENT (12, toPretty p))]))
	(true, STR "") predicateList in
      pp
    | PostConditional (guard, consequent) ->
       LBLOCK [
           STR "if ";
           precondition_to_pretty guard;
           STR " then ";
	   toPretty consequent] in
  toPretty predicate

(* ----------------------------------------------------------------- read xml *)

let read_xml_postcondition 
    (node: xml_element_int)
    (parameters: fts_parameter_t list): postcondition_t =
  let get_term n = read_xml_bterm n parameters in
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
      PostRelationalExpr (op, get_term (arg 0), get_term (arg 1))
    else
      match pNode#getTag with
      | "new-memory-region" ->
         PostNewMemoryRegion (get_term (arg 0), get_term (arg 1))
      | "function-pointer" ->
         PostFunctionPointer (get_term (arg 0), get_term (arg 1))
      | "allocation-base" -> PostAllocationBase (get_term (arg 0))
      | "null" -> PostNull (get_term (arg 0))
      | "not-null" -> PostNotNull (get_term (arg 0))
      | "null-terminated" -> PostNullTerminated (get_term (arg 0))
      | "enum" -> PostEnum (get_term (arg 0), pNode#getAttribute "name")
      | "non-returning" -> PostFalse
      | "or" -> PostDisjunction (List.map aux pNode#getChildren)
      | "implies" -> PostConditional (
	read_xml_precondition_predicate 
	  ((pNode#getTaggedChild "pre")#getTaggedChild "apply") parameters,
	aux (pNode#getTaggedChild "apply"))
      | s ->
         raise_xml_error
           node
	   (LBLOCK [
                STR "Postcondition predicate ";
                STR s;
                STR " not recognized"]) in
  match (node#getTaggedChild "math")#getChild#getTag with
  | "non-returning" -> PostFalse
  | _ -> aux ((node#getTaggedChild "math")#getTaggedChild "apply")


let read_xml_postconditions 
    (node: xml_element_int)
    (parameters: fts_parameter_t list): postcondition_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n -> read_xml_postcondition n parameters) (getcc "post")


let read_xml_errorpostconditions 
    (node: xml_element_int)
    (parameters: fts_parameter_t list): postcondition_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n ->
      read_xml_postcondition n parameters) (getcc "error-post")


let read_xml_shortcut_postconditions (node:xml_element_int) =
  let zero = NumConstant numerical_zero in
  List.fold_left (fun (p,ep) n ->
    match n#getTag with
    | "post" | "error-post" -> (p,ep)
    | "enum" -> ((PostEnum (ReturnValue, n#getAttribute "name")):: p, ep)
    | "non-returning" -> (PostFalse :: p, ep)
    | "null-terminated" -> ((PostNullTerminated ReturnValue) :: p, ep)
    | "notzero-zero" | "nonzero-zero" ->
      ((PostRelationalExpr (PNotEqual,ReturnValue,zero) ) :: p,
       (PostRelationalExpr (PEquals,ReturnValue,zero) ) :: ep)
    | "zero-nonzero" | "zero-notzero" ->
      ((PostRelationalExpr (PEquals,ReturnValue,zero) ) :: p,
       (PostRelationalExpr (PNotEqual,ReturnValue,zero) ) :: ep)
    | "zero-negone" ->
      let negone = NumConstant (mkNumerical (-1)) in
      ((PostRelationalExpr (PEquals,ReturnValue,zero)) :: p,
       (PostRelationalExpr (PEquals,ReturnValue,negone) ) :: ep)
    | "zero-negative" ->
      ((PostRelationalExpr (PEquals,ReturnValue,zero)) :: p,
       (PostRelationalExpr (PLessThan, ReturnValue, zero)) :: ep)
    | "one-zero" ->
      let one = NumConstant numerical_one in
      ((PostRelationalExpr (PEquals,ReturnValue,one)) :: p,
       (PostRelationalExpr (PEquals,ReturnValue,zero) ) :: ep)  
    | "notnull" -> ((PostNotNull ReturnValue):: p, ep)
    | "notnull-null" -> 
      ((PostNotNull ReturnValue):: p, (PostNull ReturnValue) :: ep)
    | "null-notnull" ->
      ((PostNull ReturnValue) :: p, (PostNotNull ReturnValue ) :: ep)
    | "nonnegative-negone" ->
      let negone = NumConstant (mkNumerical (-1)) in
      ((PostRelationalExpr (PGreaterEqual,ReturnValue,zero)) :: p,
       (PostRelationalExpr (PEquals,ReturnValue,negone)) :: ep)
    | "nonnegative-negative" ->
      ((PostRelationalExpr (PGreaterEqual,ReturnValue,zero)) :: p,
       (PostRelationalExpr (PLessThan,ReturnValue,zero)) :: ep)
    | "positive-nonpositive" ->
      ((PostRelationalExpr (PGreaterThan,ReturnValue,zero)) :: p,
       (PostRelationalExpr (PLessEqual,ReturnValue,zero)) :: ep)
    | "positive-zero" ->
      ((PostRelationalExpr (PGreaterThan,ReturnValue,zero)) :: p,
       (PostRelationalExpr (PEquals,ReturnValue,zero)) :: ep)
    | s -> raise_xml_error n
      (LBLOCK [ STR s ; STR " not recognized as a shortcut postcondition" ]))
    ([],[]) node#getChildren


(* ---------------------------------------------------------------- operators *)

let rec modify_types_post (f:type_transformer_t) (p:postcondition_t) =
  let auxb = modify_types_bterm f in
  let auxpr = modify_types_pre f in
  let auxp = modify_types_post f in
  match p with
  | PostNewMemoryRegion (t1,t2) -> PostNewMemoryRegion (auxb t1, auxb t2)
  | PostFunctionPointer (t1, t2) -> PostFunctionPointer (auxb t1, auxb t2)
  | PostAllocationBase t -> PostAllocationBase (auxb t)
  | PostNull t -> PostNull (auxb t)
  | PostNotNull t -> PostNotNull (auxb t)
  | PostNullTerminated t -> PostNullTerminated (auxb t)
  | PostEnum (t,s) -> PostEnum (auxb t, s)
  | PostRelationalExpr (op,t1,t2) -> PostRelationalExpr (op, auxb t1, auxb t2)
  | PostDisjunction l -> PostDisjunction (List.map auxp l)
  | PostConditional (pr,p) -> PostConditional (auxpr pr, auxp p)
  | PostFalse -> PostFalse

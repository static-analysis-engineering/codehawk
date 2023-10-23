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
open Xprt

(* bchlib *)
open BCHBCTypes
open BCHBTerm
open BCHFtsParameter
open BCHLibTypes
open BCHPrecondition
open BCHTypeDefinitions
open BCHUtilities
open BCHVariableType
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

let sideeffect_to_pretty (sideEffect:sideeffect_t) =
  let rec toPretty effect =
    match effect with
    | BlockWrite (ty, x, size) ->
       LBLOCK [
           STR "block-write (";
           STR (btype_to_string ty);
	   STR ", ";
           bterm_to_pretty x;
           STR ", ";
	   bterm_to_pretty size ;
           STR ")"]
    | Modifies x             -> 
      LBLOCK [STR "modifies ("; bterm_to_pretty x; STR ")"]
    | Invalidates x          -> 
      LBLOCK [STR "invalidates ("; bterm_to_pretty x; STR ")"]
    | AllocatesStackMemory x -> 
      LBLOCK [STR "allocates-stack-memory "; bterm_to_pretty x; STR ")"]
    | StartsThread (sa,pars) ->
       LBLOCK [
           STR "starts-thread(";
           pretty_print_list pars bterm_to_pretty "(" "," ")"]
    | SetsErrno -> LBLOCK [STR "sets-errno"]
    | UnknownSideeffect -> LBLOCK [STR "unknown-sideeffect"]
    | ConditionalSideeffect (guard, consequent) ->
       LBLOCK [
           STR "if ";
           precondition_to_pretty guard;
           STR " then ";
	   toPretty consequent] in
  toPretty sideEffect

(* ----------------------------------------------------------------- read xml *)

let read_xml_par_sideeffects (node:xml_element_int):sideeffect_t list =
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
    | "block-write" -> BlockWrite (ty (),t,getsize node)
    | "block-write-null" ->
      ConditionalSideeffect (PreNotNull t, BlockWrite (ty (),t,getsize node))
    | "invalidates" -> Invalidates t 
    | "modifies" -> Modifies t
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
    (parameters: fts_parameter_t list): sideeffect_t =
  let get_term n = read_xml_bterm n parameters in
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
      BlockWrite (get_type (arg 0), get_term (arg 1), get_term (arg 2))
    | "allocates-stack-memory" -> AllocatesStackMemory (get_term (arg 0))
    | "modifies" -> Modifies (get_term (arg 0))
    | "starts-thread" ->
      StartsThread (get_term (arg 0), List.map get_term (List.tl argNodes))
    | "invalidates" -> Invalidates (get_term (arg 0))
    | "sets-errno" -> SetsErrno
    | "implies" -> ConditionalSideeffect( 
      read_xml_precondition_predicate
	((node#getTaggedChild "pre")#getTaggedChild "apply") parameters,
      aux (node#getTaggedChild "apply"))
    | s ->
       raise_xml_error
         node
         (LBLOCK [
              STR "Sideeffect predicate ";
              STR s;
              STR " not recognized"]) in
  match (node#getTaggedChild "math")#getChild#getTag with
  | "sets-errno" -> SetsErrno
  | "unknown-sideeffect" -> UnknownSideeffect
  | _ -> aux ((node#getTaggedChild "math")#getTaggedChild "apply")


let read_xml_sideeffects 
    (node: xml_element_int)
    (parameters: fts_parameter_t list): sideeffect_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n -> read_xml_sideeffect n parameters) (getcc "sideeffect")


(* ---------------------------------------------------------------- operators *)

let rec modify_types_se (f:type_transformer_t) (s:sideeffect_t) =
  let auxt = modify_type f in
  let auxb = modify_types_bterm f in
  let auxs = modify_types_se f in
  let auxp = modify_types_pre f in
  match s with
  | BlockWrite (t,t1,t2) -> BlockWrite (auxt t, auxb t1, auxb t2)
  | Modifies t -> Modifies (auxb t)
  | AllocatesStackMemory t -> AllocatesStackMemory (auxb t)
  | StartsThread (sa,pars) -> StartsThread (auxb sa, List.map auxb pars)
  | Invalidates t -> Invalidates (auxb t)
  | ConditionalSideeffect (p,s) -> ConditionalSideeffect (auxp p, auxs s)
  | SetsErrno -> SetsErrno
  | UnknownSideeffect -> UnknownSideeffect

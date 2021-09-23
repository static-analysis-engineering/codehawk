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
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open XprTypes
open XprToPretty

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHBTerm
open BCHCStructConstant
open BCHLibTypes
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

let relational_op_to_string = function
  | PEquals -> " = " 
  | PLessThan -> " < " 
  | PLessEqual -> " <= " 
  | PGreaterThan -> " > " 
  | PGreaterEqual -> " >= "
  | PNotEqual -> " != "

let relational_op_to_xml_string = function
  | PEquals -> "eq"
  | PLessThan -> "lt"
  | PLessEqual -> "leq"
  | PGreaterThan -> "gt"
  | PGreaterEqual -> "geq"
  | PNotEqual -> "neq"

let rec precondition_to_pretty (predicate:precondition_t) =
  let default name terms =
    LBLOCK [ STR name ; pretty_print_list terms bterm_to_pretty "(" ", " ")" ] in
  match predicate with
  | PreNullTerminated t -> default "null-terminated" [ t ]
  | PreNotNull t -> default "not-null" [ t ]
  | PreNull t -> default "null" [ t ]
  | PreFormatString t -> default "format-string" [ t ]
  | PreEnum (t,s,flags) -> 
     LBLOCK [
         bterm_to_pretty t;
         STR ": member of ";
         STR s;
	 if flags then STR " (flags)" else STR ""]
  | PreDerefRead (ty,x,size,b) ->
     LBLOCK [
         STR "deref-read (";
         STR (btype_to_string ty);
	 STR ",";
         bterm_to_pretty x;
         STR ",";
	 bterm_to_pretty size;
         STR (if b then ", canbenull" else ", cannotbenull");
	 STR ")"]
  | PreDerefWrite (ty,x,size,b) ->
     LBLOCK [
         STR "deref-write (";
         STR (btype_to_string ty);
	 STR ",";
         bterm_to_pretty x;
         STR ",";
	 bterm_to_pretty size;
         STR (if b then ", canbenull" else ", cannotbenull");
	 STR ")"]
  | PreFunctionPointer (ty,t) ->
     LBLOCK [
         STR "function-pointer (";
         STR  (btype_to_string ty);
         STR ", ";
	 bterm_to_pretty t;
         STR ")"]
  | PreAllocationBase t -> default "allocation-base" [ t ]
  | PreNoOverlap (t1,t2) -> default "no-overlap" [ t1 ; t2 ]
  | PreIncludes (t,sc) ->
     LBLOCK [bterm_to_pretty t; NL; cstructconstant_to_pretty sc]
  | PreRelationalExpr (op,x,y) ->
     LBLOCK [
         bterm_to_pretty x;
         STR (relational_op_to_string op);
         bterm_to_pretty y]
  | PreDisjunction predicateList ->
    let (_,pp) = List.fold_left
      (fun (first,acc) predicate ->
	(false,
         LBLOCK [
             acc;
             (if first then
                NL
              else
                LBLOCK [STR " or "; NL]);
	     INDENT (
                 12,
                 LBLOCK [
                     STR "(";
		     precondition_to_pretty predicate;
		     STR ")"])]))
      (true, STR "") predicateList in
    pp
  | PreConditional (guard, consequent) ->
     LBLOCK [
         STR "if ";
         precondition_to_pretty guard;
	 STR " then ";
         precondition_to_pretty consequent]


(* --------------------------------------------------------------- comparison *)

let rec precondition_compare p1 p2 =
  match (p1,p2) with
  | (PreNullTerminated n1, PreNullTerminated n2) -> bterm_compare n1 n2
  | (PreNullTerminated _, _) -> -1
  | (_, PreNullTerminated _) -> 1
  | (PreNotNull n1, PreNotNull n2) -> bterm_compare n1 n2
  | (PreNotNull _, _) -> -1
  | (_, PreNotNull _) -> 1
  | (PreNull n1, PreNull n2) -> bterm_compare n1 n2
  | (PreNull _, _) -> -1
  | (_, PreNull _) -> 1
  | (PreDerefRead (t1,d1,s1,b1), PreDerefRead (t2,d2,s2,b2)) ->
    let l1 = btype_compare t1 t2 in
    if l1 = 0 then 
      let l2 = bterm_compare d1 d2 in
      if l2 = 0 then 
	let l3 = bterm_compare s1 s2 in
	if l3 = 0 then Stdlib.compare b1 b2
	else l3
      else l2
    else l1
  | (PreDerefRead _, _) -> -1
  | (_, PreDerefRead _) -> 1
  | (PreDerefWrite (t1,d1,s1,b1), PreDerefWrite (t2,d2,s2,b2)) ->
    let l1 = btype_compare t1 t2 in
    if l1 = 0 then 
      let l2 = bterm_compare d1 d2 in
      if l2 = 0 then 
	let l3 = bterm_compare s1 s2 in
	if l3 = 0 then Stdlib.compare b1 b2
	else l3
      else l2
    else l1
  | (PreDerefWrite _, _) -> -1
  | (_, PreDerefWrite _) -> 1
  | (PreAllocationBase n1, PreAllocationBase n2) -> bterm_compare n1 n2
  | (PreAllocationBase _,_) -> -1
  | (_, PreAllocationBase _) -> 1
  | (PreFunctionPointer (_,t1), PreFunctionPointer (_,t2)) -> bterm_compare t1 t2
  | (PreFunctionPointer _,_) -> -1
  | (_, PreFunctionPointer _) -> 1
  | (PreNoOverlap (x1,y1), PreNoOverlap (x2,y2)) -> 
    let l1 = bterm_compare x1 x2 in if l1 = 0 then bterm_compare y1 y2 else l1
  | (PreNoOverlap _,_) -> -1
  | (_, PreNoOverlap _) -> 1
  | (PreFormatString n1, PreFormatString n2) -> bterm_compare n1 n2
  | (PreFormatString _, _) -> -1
  | (_, PreFormatString _) -> 1
  | (PreEnum (t1,s1,_), PreEnum (t2,s2,_)) -> 
    let l1 = bterm_compare t1 t2 in if l1 = 0 then Stdlib.compare s1 s2 else l1
  | (PreEnum _, _) -> -1
  | (_, PreEnum _) -> 1
  | (PreRelationalExpr (op1,x1,y1), PreRelationalExpr (op2,x2,y2)) ->
    let l1 = Stdlib.compare op1 op2 in
    if l1 = 0 then 
      let l2 = bterm_compare x1 x2 in
      if l2 = 0 then
	bterm_compare y1 y2
      else l2
    else l1
  | (PreRelationalExpr _, _) -> -1
  | (_, PreRelationalExpr _) -> 1
  | (PreDisjunction l1, PreDisjunction l2) ->
    list_compare l1 l2 precondition_compare
  | (PreDisjunction _, _) -> -1
  | (_, PreDisjunction _) -> 1
  | (PreConditional (p1,c1), PreConditional (p2,c2)) ->
    let l1 = precondition_compare p1 p2 in
    if l1 = 0 then
      precondition_compare c1 c2
    else l1
  | (PreConditional _, _) -> -1
  | (_, PreConditional _) -> 1
  | (PreIncludes(t1,sc1), PreIncludes(t2,sc2)) ->
    let l1 = bterm_compare t1 t2 in
    if l1 = 0 then cstructconstant_compare sc1 sc2 else l1
      


(* ----------------------------------------------------------------- read xml *)

let read_xml_par_preconditions (node:xml_element_int):precondition_t list =
  let zero = NumConstant numerical_zero in
  let one = IndexSize (NumConstant numerical_one) in
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let pNodes = if hasc "pre" then (getc "pre")#getChildren else [] in
  let par = read_xml_fts_parameter node in
  let t = ArgValue par in
  let ty () = match resolve_type par.apar_type with 
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
    | "null-terminated" -> PreNullTerminated t
    | "not-null" -> PreNotNull t
    | "null" -> PreNull t
    | "deref-read" ->
       let typ = ty () in
       PreDerefRead (typ, t, getsize node typ, false)
    | "deref-read-nt" -> PreDerefRead (ty (),t,ArgNullTerminatorPos t,false)
    | "deref-read-null" ->
       let typ = ty () in
       PreDerefRead (typ, t, getsize node typ, true)
    | "deref-read-null-nt" ->
       PreDerefRead (ty (), t, ArgNullTerminatorPos t, true)
    | "deref-write" ->
       let typ = ty () in
       PreDerefWrite (typ, t, getsize node typ, false)
    | "deref-write-null" ->
       let typ = ty () in
       PreDerefWrite (typ, t, getsize node typ, true)
    | "allocation-base" -> PreAllocationBase t
    | "function-pointer" ->
       let typ = ty () in PreFunctionPointer (typ, t)
    | "format-string" -> PreFormatString t
    | "includes" ->
      let name = node#getAttribute "name" in
      PreIncludes (t,get_structconstant name)  
    | "enum-value" -> 
       let flags =
         node#hasNamedAttribute "flags"
         && (node#getAttribute "flags") = "true" in
       PreEnum (t, node#getAttribute "name", flags)
    | "non-negative"
      | "nonnegative" -> PreRelationalExpr (PGreaterEqual, t, zero)
    | "positive" -> PreRelationalExpr (PGreaterThan, t, zero)
    | s ->
       raise_xml_error node
         (LBLOCK [
              STR "Parameter precondition ";
              STR s;
              STR " not recognized"]) in
  List.map aux pNodes


let is_relational_operator (op:string) =
  match op with
  | "eq" | "neq" | "gt" | "lt" | "geq" | "leq" -> true
  | _ -> false


let get_relational_operator (op:string)  =
  match op with
  | "eq"  -> PEquals
  | "neq" -> PNotEqual
  | "gt"  -> PGreaterThan
  | "lt"  -> PLessThan
  | "geq" -> PGreaterEqual
  | "leq" -> PLessEqual 
  | _ ->
    begin
      ch_error_log#add "internal error" 
	(LBLOCK [ STR "get_relational_expression: " ; STR op ]) ;
      raise (Internal_error "get_relational_expression")
    end 

let read_xml_precondition_predicate
    (node: xml_element_int)
    (parameters: fts_parameter_t list): precondition_t =
  let get_term n = read_xml_bterm n parameters in
  let get_type = read_xml_type in 
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
      PreRelationalExpr (op, get_term (arg 0), get_term (arg 1))
    else
      match pNode#getTag with
      | "or" -> PreDisjunction (List.map aux argNodes)
      | "implies" -> PreConditional (aux (arg 0), aux (arg 1))
      | "not-null" -> PreNotNull (get_term (arg 0))
      | "null" -> PreNull (get_term (arg 0))
      | "null-terminated" -> PreNullTerminated (get_term (arg 0))
      | "format-string" -> PreFormatString (get_term (arg 0))
      | "allocation-base" -> PreAllocationBase (get_term (arg 0))
      | "function-pointer" ->
         PreFunctionPointer (get_type (arg 0), get_term (arg 1))
      | "enum-value" -> 
	let flags = 
	  (pNode#hasNamedAttribute "flags")
          && (pNode#getAttribute "flags") = "true" in
	PreEnum (get_term (arg 0), pNode#getAttribute "name", flags)
      | "includes" -> 
	let sc = read_xml_cstructconstant (pNode#getTaggedChild "sc") in
	PreIncludes (get_term (arg 0), sc)
      | "deref-read" | "block-read" ->
	PreDerefRead (get_type (arg 0), get_term (arg 1), get_term (arg 2), false)
      | "deref-read-null" ->
	PreDerefRead (get_type (arg 0), get_term (arg 1), get_term (arg 2),  true)
      | "deref-read-nt" ->
	let dest = get_term (arg 1) in
	let len = ArgNullTerminatorPos dest in
	PreDerefRead (get_type (arg 0), dest, len, false)
      | "deref-read-nt-null" ->
	let dest = get_term (arg 1) in
	let len = ArgNullTerminatorPos dest in
	PreDerefRead (get_type (arg 0), dest, len, true)
      | "deref-write" ->
	PreDerefWrite (get_type (arg 0), get_term (arg 1), get_term (arg 2), false)
      | "deref-write-null" ->
	PreDerefWrite (get_type (arg 0), get_term (arg 1), get_term (arg 2), true)
      | s ->
         raise_xml_error
           node
	   (LBLOCK [
                STR "Precondition predicate symbol ";
                STR s;
                STR " not recognized"]) in
  aux node


let read_xml_precondition
    (node:xml_element_int) 
    (parameters: fts_parameter_t list): precondition_t = 
  read_xml_precondition_predicate 
    ((node#getTaggedChild "math")#getTaggedChild "apply") parameters


let read_xml_preconditions 
    (node:xml_element_int) 
    (parameters: fts_parameter_t list): precondition_t list =
  let getcc = node#getTaggedChildren in
  List.map (fun n -> read_xml_precondition n parameters) (getcc "pre")


(* ---------------------------------------------------------------- operators *)

let relational_op_to_xop = function
  | PEquals -> XEq 
  | PLessThan -> XLt
  | PLessEqual -> XLe
  | PGreaterThan -> XGt
  | PGreaterEqual -> XGe
  | PNotEqual -> XNe


let xop_to_relational_op op =
  match op with
  | XEq -> PEquals
  | XLt -> PLessThan
  | XLe -> PLessEqual
  | XGt -> PGreaterThan
  | XGe -> PGreaterEqual
  | XNe -> PNotEqual
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "expr operator ";
               STR (xop_to_string op);
	       STR " cannot be represented by a relational operator"]))


let is_relational_xop = function
  | XEq | XLt | XLe | XGt | XGe | XNe -> true
  | _ -> false


let rec modify_types_pre (f:type_transformer_t) (p:precondition_t) =
  let auxt = modify_type f in
  let auxb = modify_types_bterm f in
  let auxp = modify_types_pre f in
  match p with
  | PreNullTerminated t -> PreNullTerminated (auxb t)
  | PreNotNull t -> PreNotNull (auxb t)
  | PreNull t -> PreNull (auxb t)
  | PreDerefRead (t,t1,t2,b) -> PreDerefRead (auxt t,auxb t1,auxb t2,b)
  | PreDerefWrite (t,t1,t2,b) -> PreDerefWrite (auxt t,auxb t1,auxb t2,b)
  | PreAllocationBase t -> PreAllocationBase (auxb t)
  | PreFunctionPointer (ty,t) -> PreFunctionPointer (auxt ty, auxb t)
  | PreNoOverlap (t1,t2) -> PreNoOverlap (auxb t1, auxb t2)
  | PreFormatString t -> PreFormatString (auxb t)
  | PreEnum (t,s,flags) -> PreEnum (auxb t, s,flags)
  | PreIncludes(t,sc) -> PreIncludes (auxb t, sc)
  | PreRelationalExpr (op,t1,t2) -> PreRelationalExpr (op, auxb t1, auxb t2)
  | PreDisjunction l -> PreDisjunction (List.map auxp l)
  | PreConditional (p1,p2) -> PreConditional (auxp p1, auxp p2)

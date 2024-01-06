(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs

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
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes
open XprToPretty

let op_symbols_to_string = Hashtbl.create 23 
let op_symbols_from_string = Hashtbl.create 23

let variable_types_to_string = Hashtbl.create 11
let variable_types_from_string = Hashtbl.create 11

let add_to_table
      (toTable:('a,string) Hashtbl.t)
      (fromTable:(string,'a) Hashtbl.t)
      (stype:'a) (name:string) =
  begin
    Hashtbl.add toTable stype name ;
    Hashtbl.add fromTable name stype
  end
    
let get_string_from_table (table:('a,string) Hashtbl.t) (stype:'a) =
  if Hashtbl.mem table stype then
    Hashtbl.find table stype
  else
    raise (Invalid_argument "get_string_from_table")

let get_sumtype_from_table (table:(string,'a) Hashtbl.t) (name:string) =
  if Hashtbl.mem table name then
    Hashtbl.find table name
  else
    raise (Invalid_argument ("get_sumtype_from_table: " ^ name ^ " not found"))


let _ =
  List.iter (fun (op,s) ->
      add_to_table op_symbols_to_string op_symbols_from_string op s)
    [(XNeg, "minus" );
     (XBNot, "bnot" );
     (XBNor, "bnor" );
     (XLNot, "not" );
     (XPlus, "plus");
     (XMinus, "minus");
     (XMult, "times");
     (XDiv, "divide");
     (XMod, "rem");
     (XPow, "pow");
     (XShiftlt, "shiftleft");
     (XShiftrt, "shiftright");
     (XLsr, "lsr");
     (XAsr, "asr");
     (XLsl, "lsl");
     (XLt, "lt");
     (XGt, "gt");
     (XLe, "leq");
     (XGe, "geq");
     (XEq, "eq");
     (XNe, "neq");
     (XSubset, "subset");
     (XDisjoint, "disjoint");
     (XBAnd, "band");
     (XBXor, "bxor");
     (XBOr, "bor");
     (XLAnd, "and");
     (XLOr, "or");
     (XNumJoin, "numjoin");
     (XNumRange, "numrange");
     (XXlsb, "lsb");
     (XXlsh, "lsh");
     (Xf "buffersize", "buffersize");
     (Xf "max", "max")]


let _ =
  List.iter (fun (vt,s) ->
      add_to_table variable_types_to_string variable_types_from_string vt s)
	    [ (NUM_LOOP_COUNTER_TYPE, "LC") ;
	      (NUM_TMP_VAR_TYPE,      "TN") ;
	      (SYM_TMP_VAR_TYPE,      "TS") ;
	      (NUM_TMP_ARRAY_TYPE,    "TNA") ;
	      (SYM_TMP_ARRAY_TYPE,    "TSA") ;
	      (NUM_VAR_TYPE,          "N") ;
	      (SYM_VAR_TYPE,          "S") ;
	      (NUM_ARRAY_TYPE,        "NA") ;
	      (SYM_ARRAY_TYPE,        "SA") ]
  
let variable_type_to_string (v:variable_type_t) =
  get_string_from_table variable_types_to_string v
  
let _variable_type_from_string (s:string) =
  get_sumtype_from_table variable_types_from_string s
  
let symbol_to_xml (s:symbol_t) =
  let node = xmlElement "csymbol" in
  begin
    (if s#getSeqNumber >= 0 then node#setIntAttribute "i" s#getSeqNumber) ;
    node#setText s#getBaseName ;
    node
  end
  
let var_to_xml (v:variable_t) =
  let node = xmlElement "ci" in
  begin
    (if v#getName#getSeqNumber >= 0 then node#setIntAttribute "i" v#getName#getSeqNumber) ;
    node#setAttribute "type" (variable_type_to_string v#getType) ;
    node#setText v#getName#getBaseName ;
    node
  end
  
let symset_to_xml (l:symbol_t list) =
  let node = xmlElement "set" in
  begin
    node#appendChildren (List.map symbol_to_xml l) ;
    node
  end
  
let const_to_xml (c:xcst_t) =
  match c with
  | SymSet l -> symset_to_xml l
  | IntConst num -> xml_pretty "cn" num#toPretty
  | BoolConst b -> if b then xmlElement "true" else xmlElement "false"
  | XRandom -> xmlElement "rnd"
  | XUnknownInt -> xmlElement "rndI"
  | XUnknownSet -> xmlElement "rndS"
                 
let rec xpr_to_xml (xpr:xpr_t) =
  match xpr with
  | XVar v -> var_to_xml v
  | XConst c -> const_to_xml c
  | XOp (op, l) -> op_to_xml op l
  | XAttr (s,e) -> attr_to_xml s e
                 
and op_to_xml (op:xop_t) (l:xpr_t list) =
  let node = xmlElement "apply" in
  let opNode = xmlElement (get_string_from_table op_symbols_to_string op) in
  begin
    node#appendChildren (opNode :: (List.map xpr_to_xml l)) ;
    node
  end
  
and attr_to_xml (s:string) (e:xpr_t) =
  let node = xmlElement "apply-attr" in
  begin
    node#setAttribute "attr" s ;
    node#appendChildren [ xpr_to_xml e ] ;
    node
  end
  
let expr_to_xml (xpr:xpr_t) =
  let node = xmlElement "math" in 
  try
    begin node#appendChildren [ xpr_to_xml xpr ] ; node end
  with
  | Invalid_argument s -> 
     raise (CHFailure (LBLOCK [ STR "Error in converting " ;
                                xpr_formatter#pr_expr xpr ; 
			        STR " to xml: " ; STR s ]))
    
let _write_xml_expr (node:xml_element_int) (x:xpr_t) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let setp = node#setPrettyAttribute in
  match x with
  | XConst (IntConst n) -> set "xconst" n#toString
  | XConst (BoolConst b) -> if b then set "xbconst" "true" else set "xbconst" "false"
  | XConst XRandom -> set "xvalue" "?"
  | XConst XUnknownInt -> set "xivalue" "?"
  | XConst XUnknownSet -> set "xsvalue" "?"
  | XVar v -> 
     let index = v#getName#getSeqNumber in
     begin set "vn" v#getName#getBaseName ; if index >= 0 then seti "vx" index end
  | _ ->
     begin 
       node#appendChildren [ expr_to_xml x ] ;
       setp "xpr" (xpr_formatter#pr_expr x)
     end
    
let var_from_xml (xvar:xml_element_int) =
  let vtype = get_sumtype_from_table variable_types_from_string (xvar#getAttribute "type") in
  let name = xvar#getText in
  let vname =
    if xvar#hasNamedAttribute "i" then 
      let seqnr = xvar#getIntAttribute "i" in new symbol_t ~seqnr name
    else
      new symbol_t name in
  XVar (new variable_t vname vtype)
  
let symbol_from_xml (xsym:xml_element_int) =
  let name = xsym#getText in
  if xsym#hasNamedAttribute "i" then
    let seqnr = xsym#getIntAttribute "i" in new symbol_t ~seqnr name
  else
    new symbol_t name
  
let symset_from_xml (xset:xml_element_int) =
  SymSet (List.map symbol_from_xml xset#getChildren)
  
let rec xpr_from_xml (xxpr:xml_element_int) =
  match xxpr#getTag with
  | "ci" -> var_from_xml xxpr
  | "cn" -> XConst (IntConst (mkNumericalFromString xxpr#getText))
  | "rnd" -> XConst XRandom
  | "rndI" -> XConst XUnknownInt
  | "rndS" -> XConst XUnknownSet
  | "set" -> XConst (symset_from_xml xxpr)
  | "apply" -> op_from_xml xxpr
  | "apply-attr" -> attr_from_xml xxpr
  | "true" -> XConst (BoolConst true)
  | "false" -> XConst (BoolConst false)
  | tag ->
     raise (XmlDocumentError
              (xxpr#getLineNumber, xxpr#getColumnNumber,
	       LBLOCK [ STR "unexpected element encountered in xpr_from_xml: " ;
			STR tag ]))
    
and op_from_xml (xop:xml_element_int) =
  let children = xop#getChildren in
  if List.length children > 0 then
    let (opX,argsX) = (List.hd children, List.tl children) in
    let op = get_sumtype_from_table op_symbols_from_string opX#getTag in
    let args = List.map xpr_from_xml argsX in
    XOp (op, args)
  else
    raise (XmlDocumentError
             (xop#getLineNumber, xop#getColumnNumber,
              LBLOCK [ STR "unexpected xop element encountered in xop_from_xml" ]))
  
and attr_from_xml (xattr:xml_element_int) =
  let attr = xattr#getAttribute "attr" in
  XAttr (attr, xpr_from_xml xattr#getChild)
  
let expr_from_xml (xxpr:xml_element_int) =
  if xxpr#hasOneTaggedChild "math" then
    xpr_from_xml (xxpr#getTaggedChild  "math")#getChild
  else
    raise (XmlDocumentError
             (xxpr#getLineNumber, xxpr#getColumnNumber,
	      LBLOCK [ STR "unexpected element encountered in expr_from_xml: " ;
		       STR xxpr#getChild#getTag ; STR " (math expected)" ]))
  
let _read_xml_expr (node:xml_element_int) =
  let get = node#getAttribute in
  let getb t = let v = get t in if v = "true" then true else false in
  let geti = node#getIntAttribute in
  let getv () = 
    let name = get "vn" in
    let seqnr = geti "vx" in
    let name = new symbol_t ~seqnr name in
    new variable_t name NUM_VAR_TYPE in
  let has = node#hasNamedAttribute in
  if has "xconst" then XConst (IntConst (mkNumericalFromString (get "xconst")))
  else if has "xbconst" then XConst (BoolConst (getb "xbconst"))
  else if has "xvalue" then XConst XRandom
  else if has "xivalue" then XConst XUnknownInt
  else if has "xsvalue" then XConst XUnknownSet
  else if has "vn" then XVar (getv ()) 
  else expr_from_xml node
  

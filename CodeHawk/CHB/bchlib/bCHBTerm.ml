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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHBCTypes
open BCHLibTypes
open BCHSystemSettings
open BCHUtilities
open BCHVariableType
open BCHXmlUtil


let btype_compare = BCHBCUtil.typ_compare


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


(* ----------------------------------------------------------------- printing *)

let arithmetic_op_to_string = function
  | PPlus -> " + " 
  | PMinus -> " - " 
  | PDivide -> " / " 
  | PTimes -> " * "

let arithmetic_op_to_xml_string = function
  | PPlus -> "plus"
  | PMinus -> "minus"
  | PDivide -> "divide"
  | PTimes -> "times"

let rec bterm_to_string (t:bterm_t) =
  match t with
  | ArgValue p -> p.apar_name
  | RunTimeValue -> "runtime-value"
  | ReturnValue -> "return-value"
  | NamedConstant name -> name
  | NumConstant num -> num#toString
  | ArgBufferSize x -> "buffersize (" ^ (bterm_to_string x) ^ ")"
  | IndexSize x -> "indexsize (" ^ (bterm_to_string x) ^ ")"
  | ByteSize x -> "bytesize (" ^ (bterm_to_string x) ^ ")"
  | ArgAddressedValue (x,offset) ->
    "addressed-val (" ^ (bterm_to_string x) ^ "," ^ (bterm_to_string offset) ^ ")"
  | ArgNullTerminatorPos x ->
    "null-terminator-pos (" ^ (bterm_to_string x) ^ ")"
  | ArgSizeOf ty -> "size-of (" ^ (btype_to_string ty) ^ ")"
  | ArithmeticExpr (op, x, y) ->
     "("
     ^ (bterm_to_string x)
     ^ (arithmetic_op_to_string op)
     ^ (bterm_to_string y)
     ^ ")"


let rec bterm_to_pretty (t:bterm_t) =
  match t with
  | ArgValue p -> STR p.apar_name
  | RunTimeValue -> STR "runtime-value"
  | ReturnValue  -> STR "return-value"
  | NamedConstant name -> STR name
  | NumConstant num -> num#toPretty
  | ArgBufferSize x -> LBLOCK [STR "buffersize ("; bterm_to_pretty x; STR ")"]
  | IndexSize x -> LBLOCK [STR "indexsize ("; bterm_to_pretty x; STR ")"]
  | ByteSize x -> LBLOCK [STR "bytesize ("; bterm_to_pretty x ; STR ")"]
  | ArgAddressedValue (x,offset) ->
     LBLOCK [
         STR "addressed-val (";
         bterm_to_pretty x;
         STR ", ";
	 bterm_to_pretty offset;
         STR ")"]
  | ArgNullTerminatorPos x -> 
    LBLOCK [STR "null-terminator-pos ("; bterm_to_pretty x ; STR ")"]
  | ArgSizeOf ty -> LBLOCK [STR "size-of ("; STR (btype_to_string ty); STR ")"]
  | ArithmeticExpr (op, x, y) ->
     LBLOCK [
         STR "(";
         bterm_to_pretty x;
         STR (arithmetic_op_to_string op);
	 bterm_to_pretty y;
         STR ")"]

(* --------------------------------------------------------------- comparison *)

let rec bterm_compare n1 n2 =
  match (n1,n2) with
  | (ArgValue p1, ArgValue p2) -> fts_parameter_compare p1 p2
  | (ArgValue _, _) -> -1
  | (_, ArgValue _) -> 1
  | (RunTimeValue, RunTimeValue) -> 0
  | (RunTimeValue, _) -> -1
  | (_, RunTimeValue) -> 1
  | (ReturnValue, ReturnValue) -> 0
  | (ReturnValue, _) -> -1
  | (_, ReturnValue) -> 1
  | (NamedConstant s1, NamedConstant s2) -> Stdlib.compare s1 s2
  | (NamedConstant _, _) -> -1
  | (_, NamedConstant _) -> 1
  | (NumConstant n1, NumConstant n2) -> n1#compare n2
  | (NumConstant _,_) -> -1
  | (_, NumConstant _) -> 1
  | (ArgBufferSize nn1, ArgBufferSize nn2) -> bterm_compare nn1 nn2
  | (ArgBufferSize _, _) -> -1
  | (_, ArgBufferSize _) -> 1
  | (IndexSize nn1, IndexSize nn2) -> bterm_compare nn1 nn2
  | (IndexSize _, _) -> -1
  | (_, IndexSize _) -> 1
  | (ByteSize nn1, ByteSize nn2) -> bterm_compare nn1 nn2
  | (ByteSize _, _) -> -1
  | (_, ByteSize _) -> 1
  | (ArgAddressedValue (nn1,x1), ArgAddressedValue (nn2,x2)) ->
    let l1 = bterm_compare nn1 nn2 in
    if l1 = 0 then Stdlib.compare x1 x2 else l1
  | (ArgAddressedValue _, _) -> -1
  | (_, ArgAddressedValue _) -> 1
  | (ArgNullTerminatorPos nn1, ArgNullTerminatorPos nn2) -> bterm_compare nn1 nn2
  | (ArgNullTerminatorPos _, _) -> -1
  | (_, ArgNullTerminatorPos _) -> 1
  | (ArgSizeOf t1, ArgSizeOf t2) -> btype_compare t1 t2
  | (ArgSizeOf _, _) -> -1
  | (_, ArgSizeOf _) -> 1
  | (ArithmeticExpr (op1,x1,y1), ArithmeticExpr (op2,x2,y2)) ->
    let l1 = Stdlib.compare op1 op2 in
    if l1 = 0 then
      let l2 = bterm_compare x1 x2 in
      if l2 = 0 then
	bterm_compare y1 y2
      else l2
    else l1

and bterm_opt_compare n1 n2 =
  match (n1, n2) with
  | (None, None) -> 0
  | (None, Some _) -> -1
  | (Some _, None) -> 1
  | (Some b1, Some b2) -> bterm_compare b1 b2

(* ----------------------------------------------------------------- read xml *)

let is_arithmetic_operator (numOperator:string) =
  match numOperator with
  | "plus" | "minus" | "times" | "divide" -> true
  | _ -> false

let is_stack_parameter_term (t:bterm_t) =
  match t  with
  | ArgValue p ->
     (match p.apar_location with StackParameter _ -> true | _ -> false)
  | _ -> false

let is_global_parameter_term (t:bterm_t) =
  match t with
  | ArgValue p ->
     (match p.apar_location with GlobalParameter _ -> true | _ -> false)
  | _ -> false
  
let get_arithmetic_operator (numOperator:string) =
  match numOperator with
  | "plus" -> PPlus
  | "minus" -> PMinus
  | "times" -> PTimes
  | "divide" -> PDivide 
  | _ ->
    begin
      ch_error_log#add "internal error" 
	(LBLOCK [ STR "get_arithmetic_operator " ; STR numOperator ]) ;
      raise (Internal_error "get_arithmetic_operator")
    end

let get_parameter_reference node parameters =
  let name = node#getText in
  try
    ArgValue (List.find (fun p -> p.apar_name = name) parameters)
  with
    Not_found ->
      raise_xml_error node 
	(LBLOCK [ STR "No parameter with name " ; STR name ; 
		  STR " (parameter names: " ; 
		  pretty_print_list (List.map (fun p -> p.apar_name) parameters)
		    (fun s -> STR s) "[" "," "]" ])
      
let rec read_xml_bterm
          (node: xml_element_int) (parameters: fts_parameter_t list) =
  let read_xml_type = read_xml_type in
  let recurse n = read_xml_bterm n parameters in
  match node#getTag with
  | "runtime-value" -> RunTimeValue
  | "return-value" | "return" -> ReturnValue
  | "cn" -> NumConstant (mkNumericalFromString node#getText)
  | "ci" -> get_parameter_reference node parameters
  | "apply" ->
    let cNodes = node#getChildren in
    let opNode = List.hd cNodes in
    let argNodes = List.tl cNodes in
    let arg n =
      try List.nth argNodes n with Failure _ ->
        raise_xml_error
          node
          (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    if is_arithmetic_operator opNode#getTag then
      let op = get_arithmetic_operator opNode#getTag in
      ArithmeticExpr (op, recurse (arg 0), recurse (arg 1))
    else
      begin
	match opNode#getTag with
	| "size-of-type" -> ArgSizeOf (read_xml_type (arg 0))
	| "null-terminator-pos" -> ArgNullTerminatorPos (recurse (arg 0))
	| "buffersize" -> ArgBufferSize (recurse (arg 0))
	| "indexsize" -> IndexSize (recurse (arg 0))
	| "bytesize" -> ByteSize (recurse (arg 0))
	| "addressed-value" ->
           ArgAddressedValue (recurse (arg 0), recurse (arg 1))
	| s -> raise_xml_error
                 node (LBLOCK [ STR "Numerical term operator: " ;
				STR s ; STR " not recognized"])
      end
  | s ->
     raise_xml_error
       node 
       (LBLOCK [STR "Numerical term type "; STR s; STR " not recognized"])

(* ---------------------------------------------------------------- operators *)

let is_arithmetic_operator (numOperator:string) =
  match numOperator with
  | "plus" | "minus" | "times" | "divide" -> true
  | _ -> false


let get_arithmetic_operator (numOperator:string) =
  match numOperator with
  | "plus" -> PPlus
  | "minus" -> PMinus
  | "times" -> PTimes
  | "divide" -> PDivide 
  | _ ->
    begin
      ch_error_log#add
        "internal error" 
	(LBLOCK [ STR "get_arithmetic_operator " ; STR numOperator ]) ;
      raise (Internal_error "get_arithmetic_operator")
    end


let arithmetic_op_to_xop = function
  | PPlus -> XPlus
  | PMinus -> XMinus
  | PDivide -> XDiv
  | PTimes -> XMult


let xop_to_arithmetic_op op =
  match op with
  | XPlus -> PPlus
  | XMinus -> PMinus
  | XDiv -> PDivide
  | XMult -> PTimes
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "expr operator ";
               STR (xop_to_string op);
	       STR " cannot be represented by an arithmetic operator"]))


let is_arithmetic_xop = function
  | XPlus | XMinus | XDiv | XMult -> true
  | _ -> false


let rec xpr_to_bterm (xpr:xpr_t) (subst:variable_t -> bterm_t) =
  match xpr with
  | XConst XRandom | XConst XUnknownInt | XConst XUnknownSet -> None
  | XConst (IntConst n) -> Some (NumConstant n)
  | XOp (xop, [ x ; y ]) ->
    if is_arithmetic_xop xop then
      match (xpr_to_bterm x subst, xpr_to_bterm y subst) with
	(Some nx, Some ny) ->
	  Some (ArithmeticExpr (xop_to_arithmetic_op xop, nx, ny))
      | _ -> None
    else
      begin
	(if collect_diagnostics () then
           ch_diagnostics_log#add
             "xpr to bterm failure" (xpr_formatter#pr_expr xpr));
	None
      end
  | XVar v -> 
     let nv = subst v in
     begin match nv with RunTimeValue -> None | _ -> Some nv end
  | _ -> None


let mk_global_parameter_term
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      (gaddr:doubleword_int) =
  ArgValue (mk_global_parameter ~btype ~desc ~roles ~io ~size gaddr)


let mk_stack_parameter_term
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      (arg_index:int) =
  ArgValue (mk_stack_parameter ~btype ~desc ~roles ~io ~size arg_index)


let rec modify_types_bterm (f:type_transformer_t) (t:bterm_t) =
  let aux = modify_types_bterm f in
  match t with
  | ArgValue p -> ArgValue (modify_types_par f p)
  | ArgBufferSize t -> ArgBufferSize (aux t)
  | IndexSize t -> IndexSize (aux t)
  | ByteSize t -> ByteSize (aux t)
  | ArgAddressedValue (t1,t2) -> ArgAddressedValue (aux t1, aux t2)
  | ArgNullTerminatorPos t -> ArgNullTerminatorPos (aux t)
  | ArgSizeOf t -> ArgSizeOf (modify_type f t)
  | ArithmeticExpr (op,t1,t2) -> ArithmeticExpr (op,aux t1, aux t2)
  | _ -> t


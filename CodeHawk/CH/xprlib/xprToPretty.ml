(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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
open CHPretty

(* xprlib *)
open XprTypes

let xop_to_string = function
  | XNeg     -> "-"
  | XBNot    -> "~"
  | XLNot    -> "not"
  | XPlus    -> "+"
  | XMinus   -> "-"
  | XMult    -> "*"
  | XDiv     -> "/"
  | XMod     -> "mod"
  | XPow     -> "**"
  | XShiftlt -> "shift_left"
  | XShiftrt -> "shift_right"
  | XLsr     -> ">>"
  | XAsr     -> "s>>"
  | XLsl     -> "<<"
  | XLt      -> "<"
  | XGt      -> ">"
  | XLe      -> "<="
  | XGe      -> ">="
  | XEq      -> "="
  | XNe      -> "!="
  | XSubset  -> "in"
  | XDisjoint -> "disjoint"
  | XBAnd    -> "bitwise_and"
  | XBXor    -> "bitwise_xor"
  | XBOr     -> "bitwise_or"
  | XBNor    -> "bitwise_nor"
  | XLAnd    -> "and"
  | XLOr     -> "or"
  | XNumJoin -> "(+)"
  | XNumRange -> "<+>"
  | XXlsb    -> "lsb"
  | XXlsh    -> "lsh"
  | XXbyte   -> "xbyte"
  | Xf s     -> "f_" ^ s


class xpr_pretty_printer_t:xpr_pretty_printer_int =
object (self)
  
  method private pr_op op = STR (xop_to_string op)

  method private pr_const c = 
    match c with
    | SymSet [s] -> s#toPretty
    | SymSet l -> pretty_print_list l (fun s -> s#toPretty) "[" "," "]"
    | IntConst n -> n#toPretty
    | BoolConst true ->  STR "true"
    | BoolConst false -> STR "false"
    | XRandom -> STR "Unknown"
    | XUnknownInt -> STR "?i?"
    | XUnknownSet -> STR "?s?"


  method pr_expr e =
    match e with
    | XVar v -> v#toPretty
    | XConst c -> self#pr_const c
    | XOp (op, l) ->
       LBLOCK [
	   STR "(" ; self#pr_op op ; STR " " ; 
	   pretty_print_list l self#pr_expr "" "," "" ;
	   STR ")" ]
      | XAttr (s,e) -> LBLOCK [ STR s ; STR " of " ; self#pr_expr e ]

end


class xpr_formatter_t attr_printer sym_printer var_printer:xpr_pretty_printer_int =
object (self)

  method private pr_const c = 
    match c with
    | SymSet [s] -> sym_printer s
    | SymSet l -> pretty_print_list l (fun s -> sym_printer s) "[" "," "]"
    | IntConst n -> n#toPretty
    | BoolConst true ->  STR "true"
    | BoolConst false -> STR "false"
    | XRandom -> STR "Unknown"
    | XUnknownInt -> STR "?i?"
    | XUnknownSet -> STR "?s?"

  method pr_expr e =
    match e with
    | XVar v -> var_printer v
    | XConst c -> self#pr_const c
    | XOp (op,l) -> self#pr_op op l
    | XAttr (s,e) -> 
       let (p1,p2) = attr_printer s in
       LBLOCK [ p1 ; self#pr_expr e ; p2 ]

  method private pr_op op l =
    match l with
    | [e1; e2] ->
       let f1 = self#pr_expr e1 in
       let f2 = self#pr_expr e2 in
       let wrap p = LBLOCK [STR "("; f1; p; f2; STR ")"] in
       begin
	 match op with
	 | XPlus -> wrap (STR " + ")
	 | XMinus -> wrap (STR " - ")
	 | XMult -> wrap (STR " * ")
	 | XDiv -> wrap (STR " / ")
	 | XMod -> wrap (STR " % ")
         | XPow -> wrap (STR " ** ")
	 | XShiftlt -> wrap (STR " << ")
	 | XShiftrt -> wrap (STR " >> ")
         | XLsr -> wrap (STR " >> ")
         | XAsr -> wrap (STR " s>> ")
         | XLsl -> wrap (STR " << ")
	 | XLt -> wrap (STR " < ")
	 | XGt -> wrap (STR " > ")
	 | XLe -> wrap (STR  " <= ")
	 | XGe -> wrap (STR " >= ")
	 | XEq -> wrap (STR " = ")
	 | XNe -> wrap (STR " != ")
	 | XSubset -> wrap (STR " in ")
	 | XDisjoint -> wrap (STR " disjoint with ")
	 | XBAnd -> wrap (STR " & ")
	 | XBOr -> wrap (STR " | ")
	 | XBXor -> wrap (STR " xor ")
         | XBNor -> wrap (STR " nor ")
	 | XLAnd -> wrap (STR " and ")
	 | XLOr -> wrap (STR " or ")
         | XXbyte -> wrap (STR " xbyte ")
	 | XNumJoin -> wrap (STR " (+) ")
	 | XNumRange ->
	    LBLOCK [ STR "[" ; f1 ; STR " .. " ; f2 ; STR "]" ]
	 | Xf s -> LBLOCK [ STR s ; STR " (" ; f1 ; STR ", " ; f2 ; STR ")" ]
	 | _ ->
	    begin
	      pr_debug [
		  STR "Unrecognized expression in two-argument pr_op: ";
                  STR (xop_to_string op)];
	      failwith ("CExprToPretty: pr_op " ^ (xop_to_string op))
	    end
       end
    | [e] ->
       let f = self#pr_expr e in
       let wrap p = LBLOCK [STR "("; p; f; STR ")"] in
       begin
	 match op with
	 | XNeg -> wrap (STR "-")
	 | XBNot -> wrap (STR " b-not ")
	 | XLNot -> wrap (STR " not ")
	 | XNumJoin -> wrap (STR " (+) ")
	 | XNumRange -> wrap (STR " <+> ")
         | XXlsb -> wrap (STR "lsb ")
         | XXlsh -> wrap (STR "lsh ")
	 | Xf s -> LBLOCK [STR s; STR " ("; f; STR ")"]
	 | _ ->
	    begin
	      pr_debug [
	          STR "Unrecognized expression in single-argument pr_op: ";
                  STR (xop_to_string op)];
	      failwith ("CExprToPretty: pr_op " ^ (xop_to_string op))
	    end
	   
       end
    | [] -> 
       begin
	 pr_debug [STR "Empty operand list in pr_op"];
	 failwith "CExprToPretty: pr_op"
       end
      
    | _ ->
       let fs = List.map self#pr_expr l in
       let fs = LBLOCK (List.map (fun p -> LBLOCK [p; STR ", "]) fs) in
       let wrap p = LBLOCK [STR "("; p; fs; STR ")"] in
       begin
	 match op with
	 | XLt | XGt | XLe | XGe  -> wrap (STR "ptr_op")
	 | XNumJoin | XNumRange -> wrap (STR (xop_to_string op))
	 | Xf s -> LBLOCK [STR s; pretty_print_list l self#pr_expr "(" "," ")" ]
	 | _ ->
	    begin
	      pr_debug [
                  STR "Unrecognized expression in multiple-argument pr_op: ";
                  STR (xop_to_string op)];
	      failwith ("CExprToPretty: pr_op " ^ (xop_to_string op))
	    end
       end
       
end
  
let default_attr_to_pretty s = ((LBLOCK [ STR s ; STR " of "] ), (STR ""))

let default_sym_to_pretty s = STR s#getBaseName

let default_var_to_pretty v = STR v#getName#getBaseName

let xpr_printer = new xpr_pretty_printer_t

let xpr_formatter =
  new xpr_formatter_t
    default_attr_to_pretty default_sym_to_pretty default_var_to_pretty

let _xpr_formatter_customized f = new xpr_formatter_t f

let make_xpr_formatter symPrinter varPrinter =
  new xpr_formatter_t default_attr_to_pretty symPrinter varPrinter

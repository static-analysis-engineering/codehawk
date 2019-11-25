(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHLanguage

(* chutil *)
open CHLogger
open CHNestedCommands

(* xprlib *)
open Xprt
open XprTypes
open XprUtil
open Xsimplify

(* cchlib *)
open CCHUtilities


let sym_constant s = SymSet [ s ]

let null_symbol = new symbol_t ~seqnr:(-1) "NULL"
let null_constant = sym_constant null_symbol
let null_constant_expr = XConst null_constant

let null_set_constant = SymSet [ null_symbol ]
let null_set_constant_expr = XConst null_set_constant

let unknown_address_symbol = new symbol_t ~seqnr:(-2) "unknown address"

(* negate_bool overapproximates using a lattice with Random as Top *)
let rec negate_bool expr =
  match expr with
  | XConst (BoolConst b) -> 
      XConst (BoolConst (not b))
  | XConst (XRandom) -> 
    XConst (XRandom)
  | XVar _ -> 
    XOp (XNe , [expr ; zero_constant_expr])
  | XOp (op, [e]) ->
    begin
      match op with
	XLNot -> e
      | XNeg -> negate_bool e
      | XBNot -> random_constant_expr
      | _ ->
	begin
	  ch_error_log#add
            "invocation error" 
	    (STR "Unexpected operator in unary expression in negate_bool");
	  raise (CCHFailure (STR "CExpr.negate_bool"))
	end
    end
  | XOp (op, [e1;e2]) ->
    begin
      match op with
	XLt -> XOp (XGe , [e1;e2])
      | XGt -> XOp (XLe , [e1;e2])
      | XLe -> XOp (XGt , [e1;e2])
      | XGe -> XOp (XLt , [e1;e2])
      | XEq -> XOp (XNe , [e1;e2])
      | XNe -> XOp (XEq , [e1;e2])
      | XSubset -> XOp (XDisjoint, [e1;e2])
      | XDisjoint -> XOp (XSubset, [e1;e2])
      | _ -> XOp (XEq, [expr ; zero_constant_expr])
	
    end
  | XOp (XGe, l) -> XOp (XLt, l)
  | XOp (XGt, l) -> XOp (XLe, l)
  | XOp (XLt, l) -> XOp (XGe, l)
  | XOp (XLe, l) -> XOp (XGt, l)
  | _ -> 
    begin
      ch_error_log#add "invocation error" (STR "Unknown expression in negate_bool") ;
      raise (CCHFailure (STR "CExpr.negate_bool"))
    end
      
      
let cexpr_2_symvar (reqS:tmp_provider_t) (reqC:cst_provider_t) (cexpr:xpr_t):code_var_t =
  match cexpr with
    XVar v ->
      (make_nested_nop (), v)
  | XConst (SymSet [s]) ->
    let tmp = reqS () in
    let assign = make_nested_cmd (ASSIGN_SYM (tmp, SYM s)) in
    (assign, tmp)
  | _ ->
    let tmp = reqS () in
    (make_nested_nop (), tmp)
      
let cexpr2symvar (reqS:tmp_provider_t) (reqC:cst_provider_t) (cexpr:xpr_t):code_var_t =
  let (_, sim_expr) = simplify_expr cexpr in
  cexpr_2_symvar reqS reqC sim_expr
    

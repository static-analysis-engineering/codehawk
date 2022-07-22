(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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
open CHBounds
open CHCommon
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty               
open CHSymbolicSets
open CHUtils

(* chutil *)
open CHUtil

(* xprlib *)
open XprTypes

exception XprFailure of string * pretty_t

let sym_constant s = SymSet [s]
let sym_constant_expr s = XConst (sym_constant s)

let sym_set_constant l = SymSet l
let sym_set_constant_expr l = XConst (sym_set_constant l)

let zero_constant = IntConst (numerical_zero)
let zero_constant_expr = XConst (zero_constant)

let one_constant = IntConst (mkNumerical 1)
let one_constant_expr = XConst (one_constant)

let int_constant i = IntConst (mkNumerical i)
let int_constant_expr i = XConst (int_constant i)
let num_constant_expr n = XConst (IntConst n)

let big_int_constant i = IntConst (mkNumerical_big i)
let big_int_constant_expr i = XConst (big_int_constant i)

let random_constant_expr = XConst XRandom
let unknown_int_constant_expr = XConst XUnknownInt

let interval_expr i =
  match i#singleton with 
    Some num -> num_constant_expr num
  | _ ->
    let minb = i#getMin#getBound in
    let maxb = i#getMax#getBound in
    match (minb, maxb) with
    | (NUMBER minv, NUMBER maxv) -> 
       XOp (XNumRange, [ num_constant_expr minv ; num_constant_expr maxv ])
    | (NUMBER minv, _) ->
       XOp (XNumRange, [ num_constant_expr minv ; unknown_int_constant_expr])
    | (_, NUMBER maxv) ->
       XOp (XNumRange, [ unknown_int_constant_expr ; num_constant_expr maxv])
    | _ -> 
       random_constant_expr
	
let unknown_set_constant_expr = XConst XUnknownSet
  
let true_constant = BoolConst true
let true_constant_expr = XConst true_constant
  
let false_constant = BoolConst false
let false_constant_expr = XConst false_constant
  
let is_random = function XConst XRandom -> true | _ -> false
	
let is_true = function
  | XConst (BoolConst b) -> b
  | _ -> false
       
let is_false = function
  | XConst (BoolConst b) -> not b
  | _ -> false
       
let get_bool expr =
  match expr with
  | XConst (BoolConst b) -> b
  | _ ->
     raise (XprFailure
	      ("CExpr.get_bool",
	       LBLOCK [STR "not a boolean constant in get_bool: " ]))

let is_zero = function
  | XConst (IntConst num) -> num#equal numerical_zero
  | _ -> false

let is_one = function
  | XConst (IntConst num) -> num#equal numerical_one
  | _ -> false

let is_non_zero_int = function
  | XConst (IntConst num) -> not (num#equal numerical_zero)
  | _ -> false

let is_intconst = function
  | XConst (IntConst _ ) -> true
  | _ -> false

let is_conjunction = function
    XOp (XLAnd, _) -> true
  | _ -> false

let is_disjunction = function
  | XOp (XLOr, _) -> true
  | _ -> false

let get_conjuncts = function
  | XOp (XLAnd, c) -> c
  | _ -> raise (XprFailure
		  ("Xprt.get_conjuncts",
		   LBLOCK [ STR "not a conjunction in get_conjuncts: "]))

let get_disjuncts = function
  | XOp (XLOr, d) -> d
  | _ -> raise (XprFailure
		  ("Xprt.get_disjuncts",
		   LBLOCK [ STR "not a disjunction in get_disjuncts: "]))

let get_const = function
  | XConst (IntConst num) -> Some num
  | XConst (BoolConst b) -> 
      if b then Some numerical_one else Some numerical_zero
  | _ -> None

let get_sym_const = function
  | XConst (SymSet [s]) -> Some s
  | _ -> None

let get_sym_set = function
  | XConst (SymSet l) -> Some l
  | _ -> None

let make_ch_symbolic_set = function
  | XConst (SymSet l) -> new symbolic_set_t l
  | _ -> topSymbolicSet

let is_bool_op = function
  | XLt
  | XGt
  | XLe
  | XGe
  | XEq
  | XNe 
  | XSubset
  | XDisjoint
  | XLAnd
  | XLOr -> true
  | _ -> false

let is_numeric_bool_op = function
  | XLt
  | XGt
  | XLe
  | XGe
  | XNe
  | XEq -> true
  | _ -> false

let is_symbolic_bool_op = function
  | XSubset
  | XDisjoint -> true
  | _ -> false

type engine_expr_type_t =
  | NumericType
  | SymbolicType
  | BoolType

let engine_type_of_var v = 
  if is_numerical_type v#getType then NumericType else SymbolicType

let engine_type_of_const = function
  | SymSet _
  | XUnknownSet -> SymbolicType
  | XUnknownInt
  | IntConst _ -> NumericType
  | BoolConst _ 
  | XRandom -> BoolType

let vars_in_expr (expr:xpr_t):VariableCollections.set_t =
  let s = new VariableCollections.set_t in
  let rec vs e =
    match e with
    | XVar v -> s#add v
    | XConst _ -> ()
    | XOp (_, l) -> List.iter vs l
    | XAttr (_,e) -> vs e in
  begin
    vs expr;
    s
  end

let variables_in_expr (x:xpr_t):variable_t list = (vars_in_expr x)#toList

let vars_in_expr_list (exprs:xpr_t list) =
  let s = new VariableCollections.set_t in
    begin 
      List.iter (fun e -> s#addSet (vars_in_expr e)) exprs;
      s#toList
    end

let syntactically_equal expr1 expr2 =
  let c_equal c1 c2 =
    match (c1,c2) with
    | (SymSet s1, SymSet s2) -> List.for_all2 (fun x1 x2 -> x1#equal x2) s1 s2
    | (IntConst n1, IntConst n2) -> n1#equal n2
    | (BoolConst b1, BoolConst b2) -> b1 = b2
    | _ -> false in
  let rec e_equal e1 e2 =
    match (e1,e2) with
    | (XVar v1, XVar v2) -> v1#equal v2
    | (XConst c1, XConst c2) -> c_equal c1 c2
    | (XOp (op1,l1), XOp (op2,l2)) ->
      (op1 = op2) && (List.length l1 = List.length l2) &&
	List.for_all2 (fun x1 x2 -> e_equal x1 x2) l1 l2
    | (XAttr (s1,e1'), XAttr(s2,e2')) -> s1 = s2 && e_equal e1' e2'
    | _ -> false in
  e_equal expr1 expr2


let op_strings =
  [(XNeg, "XNeg");
   (XBNot, "XBNot");
   (XLNot, "XLNot");
   (XPlus, "XPlus");
   (XMinus, "XMinus");
   (XMult, "XMult");
   (XDiv, "XDiv");
   (XMod, "XMod");
   (XShiftlt, "XShiftlt");
   (XShiftrt, "XShiftrt");
   (XLsr, "XLsr");
   (XAsr, "XAsr");
   (XLsl, "XLsl");
   (XLt, "XLt");
   (XGt, "XGt");
   (XGe, "XGe");
   (XLe, "XLe");
   (XEq, "XEq");
   (XNe, "XNe");
   (XSubset, "XSubset");
   (XDisjoint, "XDisjoint");
   (XBAnd, "XBAnd");
   (XBXor, "XBXOr");
   (XLAnd, "XLAnd");
   (XLOr, "XLOr");
   (XBOr, "XBOr");
   (XBNor, "XBNor");
   (XNumJoin, "XNumJoin");
   (XNumRange, "XNumRange");
   (Xf "","Xf")]


let get_op_string op = 
  try
    let (_,s) = List.find (fun (o,s) -> op = o) op_strings in s
  with
  | Not_found ->
     raise (CHFailure (LBLOCK [STR  "Operator not found in get_op_string"]))


let compare_op op1 op2 =
  let op1_string = get_op_string op1 in
  let op2_string = get_op_string op2 in
  Stdlib.compare op1_string op2_string


let syntactic_comparison expr1 expr2 =
  let c_compare c1 c2 =
    match (c1,c2) with
    | (SymSet s1, SymSet s2) -> 
       let l = Stdlib.compare (List.length s1) (List.length s2) in
       if l = 0 then
	 list_compare s1 s2 (fun x y -> x#compare y)
       else
	 l
    | (IntConst c1, IntConst c2) -> c1#compare c2
    | (BoolConst b1, BoolConst b2) ->
       begin
	 match (b1,b2) with
	 | (false, false) 
	   | (true, true) -> 0
	 | (false, true) -> -1
	 | (true, false) -> 1
       end
    | (XRandom,XRandom) -> 0
    | (XRandom, _) -> -1
    | (_, XRandom) -> 1
    | (XUnknownInt,XUnknownInt) -> 0
    | (XUnknownInt, _) -> -1
    | (_, XUnknownInt) -> 1
    | (XUnknownSet,XUnknownSet) -> 0
    | (XUnknownSet, _) -> -1
    | (_, XUnknownSet) -> 1
    | (BoolConst _, _) -> -1
    | (_, BoolConst _) -> 1
    | (IntConst _, _) -> -1
    | (_, IntConst _) -> 1 in
  let rec e_compare e1 e2 =
    match (e1,e2) with
      (XConst c1, XConst c2) -> c_compare c1 c2
    | (XVar v1, XVar v2) -> v1#compare v2
    | (XOp (op1, l1), XOp (op2, l2)) -> 
       let l = compare_op op1 op2 in
       if l = 0 then list_compare l1 l2 e_compare else l
    | (XAttr (s1,ee1), XAttr (s2,ee2)) ->
       let l = Stdlib.compare s1 s2 in if l = 0 then e_compare ee1 ee2 else l
    | (XConst _, _) -> -1
    | (_, XConst _) -> 1
    | (XVar _, _) -> -1
    | (_, XVar _) -> 1
    | (XOp _, _) -> -1
    | (_, XOp _) -> 1 in
  e_compare expr1 expr2
  
  
let rec num_terms e = 
  match e with
    XVar _ | XConst _ | XAttr _ -> 1
    | XOp (XPlus, l) | XOp (XMinus, l) ->
       List.fold_left (fun a x -> a + (num_terms x)) 0 l
    | _ -> 1
         

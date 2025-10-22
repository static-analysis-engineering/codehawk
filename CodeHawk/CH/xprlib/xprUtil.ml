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
open CHCommon
open CHLanguage
open CHNumerical
open CHPEPRTypes
open CHPretty

(* chutil *)
open CHNestedCommands

(* xprlib *)
open Xprt
open XprTypes
open Xsimplify

(* ===============================================================================
   Conversion of xpr_t to engine expressions + code
   ===============================================================================
 *)

let xconst_2_numexpr (reqN:tmp_provider_t) (_reqC:cst_provider_t) (c:xcst_t):code_num_t =
    match c with
    | IntConst num -> (make_nested_nop (), NUM num)
    | BoolConst b ->
        let num = if b then numerical_one else numerical_zero in
        (make_nested_nop (), NUM num)
    | _ -> (make_nested_nop (), NUM_VAR (reqN ()))


let xconst_2_boolexpr (_reqN:tmp_provider_t) (_reqC:cst_provider_t) (c:xcst_t):code_bool_t =
    let bxpr = match c with
    | BoolConst b -> if b then TRUE else FALSE
    | IntConst num -> if num#equal numerical_zero then FALSE else TRUE
    | _ -> RANDOM in
    (make_nested_nop (), bxpr)


let rec xpr_2_numexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (xpr:xpr_t):code_num_t =
    match xpr with
      XVar v -> (make_nested_nop (), NUM_VAR v)
    | XConst c -> xconst_2_numexpr reqN reqC c
    | XOp (op, l) -> xop_2_numexpr reqN reqC op l
    | XAttr _ -> (make_nested_nop (), NUM_VAR (reqN ()))


and xop_2_numexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (op:xop_t) (l:xpr_t list):code_num_t =
    match (op,l) with
    | (_, []) ->
       raise (CHFailure (LBLOCK [STR "Empty operand list in xop_2_numexpr"]))

    | (XNeg, [e]) ->
       xpr_2_numexpr reqN reqC (XOp (XMinus, [zero_constant_expr; e]))

    | (XLNot, [_e])
    | (XBNot, [_e])
    | (XXlsb, [_e])
    | (XXlsh, [_e]) ->
       (make_nested_nop (), NUM_VAR (reqN ()))

    | (XMult, [XConst (IntConst n); XVar v])
      | (XMult, [XVar v; XConst (IntConst n)]) when n#equal (mkNumerical 2) ->
       (make_nested_nop () , PLUS (v, v))

    | (XMult, [XConst (IntConst n); XVar v])
      | (XMult, [XVar v; XConst (IntConst n)]) when n#equal (mkNumerical 4) ->
       let tmp = reqN () in
       let asgn1 = make_nested_cmd (ASSIGN_NUM (tmp, PLUS (v,v))) in
       let asgn2 = make_nested_cmd (ASSIGN_NUM (tmp, PLUS (tmp,tmp))) in
       (make_nested_cmd_block [asgn1; asgn2], NUM_VAR tmp)

    | (XMult, [XConst (IntConst n); XVar v])
      | (XMult, [XVar v; XConst (IntConst n)]) when n#equal (mkNumerical 8) ->
       let tmp1 = reqN () in
       let tmp2 = reqN () in
       let asgn1 = make_nested_cmd (ASSIGN_NUM (tmp1, PLUS (v,v))) in
       let asgn2 = make_nested_cmd (ASSIGN_NUM (tmp2, PLUS (tmp1,tmp1))) in
       let asgn3 = make_nested_cmd (ASSIGN_NUM (tmp2, PLUS (tmp2,tmp2))) in
       (make_nested_cmd_block [asgn1; asgn2; asgn3], NUM_VAR tmp2)

    | (XMult, [XConst (IntConst n); XVar v])
      | (XMult, [XVar v; XConst (IntConst n)]) when n#equal (mkNumerical 16) ->
       let tmp1 = reqN () in
       let tmp2 = reqN () in
       let tmp3 = reqN () in
       let asgn1 = make_nested_cmd (ASSIGN_NUM (tmp1, PLUS (v,v))) in
       let asgn2 = make_nested_cmd (ASSIGN_NUM (tmp2, PLUS (tmp1,tmp1))) in
       let asgn3 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp2,tmp2))) in
       let asgn4 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp3,tmp3))) in
       (make_nested_cmd_block [asgn1; asgn2; asgn3; asgn4], NUM_VAR tmp3)

    | (XMult, [XConst (IntConst n); XVar v])
      | (XMult, [XVar v; XConst (IntConst n)]) when n#equal (mkNumerical 16) ->
       let tmp1 = reqN () in
       let tmp2 = reqN () in
       let tmp3 = reqN () in
       let tmp4 = reqN () in
       let asgn1 = make_nested_cmd (ASSIGN_NUM (tmp1, PLUS (v,v))) in
       let asgn2 = make_nested_cmd (ASSIGN_NUM (tmp2, PLUS (tmp1,tmp1))) in
       let asgn3 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp2,tmp2))) in
       let asgn4 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp3,tmp3))) in
       let asgn5 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp4,tmp4))) in
       (make_nested_cmd_block [asgn1; asgn2; asgn3; asgn4; asgn5], NUM_VAR tmp4)

    | (XMult, [XConst (IntConst n); XVar v])
      | (XMult, [XVar v; XConst (IntConst n)]) when n#equal (mkNumerical 32) ->
       let tmp1 = reqN () in
       let tmp2 = reqN () in
       let tmp3 = reqN () in
       let tmp4 = reqN () in
       let tmp5 = reqN () in
       let asgn1 = make_nested_cmd (ASSIGN_NUM (tmp1, PLUS (v,v))) in
       let asgn2 = make_nested_cmd (ASSIGN_NUM (tmp2, PLUS (tmp1,tmp1))) in
       let asgn3 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp2,tmp2))) in
       let asgn4 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp3,tmp3))) in
       let asgn5 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp4,tmp4))) in
       let asgn6 = make_nested_cmd (ASSIGN_NUM (tmp3, PLUS (tmp5,tmp5))) in
       (make_nested_cmd_block [asgn1; asgn2; asgn3; asgn4; asgn5; asgn6], NUM_VAR tmp5)

    | (XPlus,   [e1; e2])
    | (XMinus,  [e1; e2])
    | (XMult,   [e1; e2])
    | (XDiv,    [e1; e2]) ->
      let (c1,r1) = xpr_2_numvar reqN reqC e1 in
      let (c2,r2) = xpr_2_numvar reqN reqC e2 in
      let num_expr =
        match op with
        | XPlus  -> PLUS  (r1, r2)
        | XMinus -> MINUS (r1, r2)
        | XMult  -> MULT  (r1, r2)
        | XDiv   -> DIV   (r1, r2)
        | _ ->
           failwith "Unexpected operator in xop_2_numexpr" in
      (make_nested_cmd_block [c1; c2], num_expr)

    | (XMod, [XConst (IntConst n1); XConst (IntConst n2)]) ->
       (make_nested_nop (), NUM (n1#modulo n2))

    | (XNumRange, [e1; e2]) ->
        let tmp = reqN () in
        let lb = XOp (XGe, [XVar tmp; e1]) in
        let ub = XOp (XLe, [XVar tmp; e2]) in
        let (lbc,lbe) = xpr_2_boolexpr reqN reqC lb in
        let (ubc,ube) = xpr_2_boolexpr reqN reqC ub in
        let lba = make_nested_cmd (ASSERT lbe) in
        let uba = make_nested_cmd (ASSERT ube) in
        let code = make_nested_cmd_block [lbc; ubc; lba; uba] in
          (code, NUM_VAR tmp)

    | _ ->
      (make_nested_nop (), NUM_VAR (reqN ()))


and xpr_2_numvar (reqN:tmp_provider_t) (reqC:cst_provider_t) (xpr:xpr_t):code_var_t =
    match xpr with
    | XVar v ->
       (make_nested_nop (), v)
    | XConst (IntConst n) ->
       let v = reqC n in (make_nested_nop (), v)
    | _ ->
       let (c,r) = xpr_2_numexpr reqN reqC xpr in
       let tmp = reqN () in
       let asgn = make_nested_cmd (ASSIGN_NUM (tmp, r)) in
       let code = make_nested_cmd_block [c; asgn] in
         (code, tmp)


and xpr_2_boolexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (xpr:xpr_t):code_bool_t =
    match xpr with
    | XVar v -> xvar_2_boolexpr reqN reqC v
    | XConst c -> xconst_2_boolexpr reqN reqC c
    | XOp (op, l) -> xop_2_boolexpr reqN reqC op l
    | _ ->
      raise (CHFailure (LBLOCK [STR "Unexpected expression in expr_2_boolexpr"]))


and xvar_2_boolexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (v:variable_t):code_bool_t =
    let bxpr =
      if v#isNumerical then
	XOp (XNe, [XVar v; zero_constant_expr])
      else
	XConst XRandom in
    xpr_2_boolexpr reqN reqC bxpr


and xop_2_boolexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (op:xop_t) (l:xpr_t list) =
  let default = (make_nested_nop (), RANDOM) in
  match (op, l) with
    (_, []) ->
      raise (CHFailure (STR "Empty operand list in xop_2_boolexpr"))

  | (XNeg, [_e]) ->
      xpr_2_boolexpr reqN reqC (XOp (XNe, [XOp (op, l); zero_constant_expr]))
  | (XLNot, [_e])
  | (XBNot, [_e])
  | (XXlsb, [_e])
  | (XXlsh, [_e]) ->
      default

  | (XDisjoint, [XVar v; XConst (SymSet l)]) ->
      (make_nested_nop (), DISJOINT (v,l))

  | (XSubset, [XVar v; XConst (SymSet l)]) ->
      (make_nested_nop (), SUBSET (v, l))

  | (XPlus, _)
  | (XMinus, _)
  | (XMult, _)
  | (XDiv, _)
  | (XMod, _)
  | (XShiftlt, _)
  | (XShiftrt, _)
  | (XLsr, _)
  | (XAsr, _)
  | (XLsl, _) ->
      xpr_2_boolexpr reqN reqC (XOp (XNe, [XOp (op,l); zero_constant_expr]))

  | (XLt, [e1; e2])
  | (XLe, [e1; e2])
  | (XGt, [e1; e2])
  | (XGe, [e1; e2])
  | (XEq, [e1; e2])
  | (XNe, [e1; e2]) ->
      let (c1,r1) = xpr_2_numvar reqN reqC e1 in
      let (c2,r2) = xpr_2_numvar reqN reqC e2 in
      let bxpr =
	match op with
	  XLt -> LT  (r1, r2)
	| XLe -> LEQ (r1, r2)
	| XGt -> GT  (r1, r2)
	| XGe -> GEQ (r1, r2)
	| XEq -> EQ  (r1, r2)
	| XNe -> NEQ (r1, r2)
	| _ ->
	    raise (CHFailure (STR "Unexpected operator in xop_2_boolexpr"))
      in
      (make_nested_cmd_block [c1; c2], bxpr)

  | _ ->
      default


let xpr2numexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (xpr:xpr_t):code_num_t =
    let (_, sim_expr) = simplify_expr xpr in
    xpr_2_numexpr reqN reqC sim_expr


let xpr2numvar (reqN:tmp_provider_t) (reqC:cst_provider_t) (xpr:xpr_t):code_var_t =
    let (_, sim_expr) = simplify_expr xpr in
    xpr_2_numvar reqN reqC sim_expr


let xpr2boolexpr (reqN:tmp_provider_t) (reqC:cst_provider_t) (xpr:xpr_t):code_bool_t =
    let (_, sim_expr) = simplify_expr xpr in
    xpr_2_boolexpr reqN reqC sim_expr


let xpr_to_numexpr
      (reqN:tmp_provider_t)
      (reqC:cst_provider_t)
      (xpr:xpr_t):(cmd_t list * numerical_exp_t) =
  let (c,e) = xpr2numexpr reqN reqC xpr in
  (nested_cmd_2_cmds c, e)


let xpr_to_numvar
      (reqN:tmp_provider_t)
      (reqC:cst_provider_t)
      (xpr:xpr_t):(cmd_t list * variable_t) =
  let (c,v) = xpr2numvar reqN reqC xpr in
  (nested_cmd_2_cmds c, v)


let xpr_to_boolexpr
      (reqN:tmp_provider_t)
      (reqC:cst_provider_t)
      (xpr:xpr_t):(cmd_t list * boolean_exp_t) =
  let (c,e) = xpr2boolexpr reqN reqC xpr in
  (nested_cmd_2_cmds c, e)



(* ===============================================================================
   SUBSTITUTION
   =============================================================================== *)

(* type substitution_t = variable_t -> xpr_t *)

let substitute_expr (subst:substitution_t) (expr:xpr_t) =
  let rec aux exp =
    match exp with
    | XVar v -> subst v
    | XOp ((Xf "addressofvar"), _) -> exp
    | XOp (op,l) -> XOp (op, List.map (fun e -> aux e) l)
    | XAttr (s, e) -> XAttr (s, aux e)
    | _ -> exp
  in
  aux expr

let occurs_check (var:variable_t) (x:xpr_t) =
  let rec aux exp =
    match exp with
    | XVar v when v#equal var -> true
    | XVar _v -> false
    | XOp (_op,l) -> List.exists aux l
    | XAttr (_s,e) -> aux e
    | _ -> false in
  aux x


(* PEPR Conversion *)

let pepr_parameter_expr_to_xpr
      (params:pepr_params_int)
      (coeffs:coeff_vector_int)
      (n:numerical_t) =
  let factors = coeffs#get_pairs in
  simplify_xpr
    (List.fold_left (fun acc (i,c) ->
         let v = (params#nth i)#get_variable in
         XOp (XPlus, [XOp (XMult, [XVar v; num_constant_expr c]); acc]))
       (num_constant_expr n) factors)


let pex_to_xpr (params:pepr_params_int) (x:pex_int) =
  if x#is_number then
    num_constant_expr x#get_number
  else
    pepr_parameter_expr_to_xpr params x#get_k x#get_n


let pex_set_to_xpr_list (params:pepr_params_int) (s:pex_set_int):xpr_t list =
  List.map (pex_to_xpr params) s#get_s


let pex_pset_to_xpr_list_list (params:pepr_params_int) (p:pex_pset_int):xpr_t list list =
  List.map (pex_set_to_xpr_list params) p#get_p


(* disjunction of conjunction *)
let pepr_bound_to_xpr_list_list
      (params:pepr_params_int) (b:pepr_bounds_t):xpr_t list list =
  match b with
  | XTOP -> [[random_constant_expr]]
  | XPSET x -> pex_pset_to_xpr_list_list params x


let get_pepr_range_xprs
      (params:pepr_params_int) (range:pepr_range_int):pepr_xpr_extract =
  let result = {
      pepr_n = None;
      pepr_i = None;
      pepr_equalities = [];
      pepr_bounds = []
    } in
  let (range,result) =
    match range#singleton with
    | Some n -> (range#remove_singleton n, { result with pepr_n = Some n })
    | _ -> (range,result) in
  let (range,result) =
    match range#interval with
    | Some i -> (range#remove_interval i, { result with pepr_i = Some i })
    | _ -> (range,result) in
  let (range,result) =
    List.fold_left (fun (ran,_res) (k,n) ->
        (ran#remove_equality k n,
         { result with
           pepr_equalities =
             (pepr_parameter_expr_to_xpr params k n) :: result.pepr_equalities} ))
      (range, result) range#parameter_exprs in
  let result =
    match range#get_min#get_bound with
    | XTOP  -> result
    | b -> { result with
             pepr_bounds =
               (LB,pepr_bound_to_xpr_list_list params b) :: result.pepr_bounds } in
  match range#get_max#get_bound with
  | XTOP -> result
  | b -> { result with
           pepr_bounds = (UB,pepr_bound_to_xpr_list_list params b) :: result.pepr_bounds }


let get_pepr_dependency_xprs
      (params:pepr_params_int) (s:param_constraint_set_int):xpr_t list =
  List.map (fun x ->
      let factors = x#get_k#get_pairs in
      let xpr =
        simplify_xpr
          (List.fold_left (fun acc (i,c) ->
               let v = (params#nth i)#get_variable in
               XOp (XPlus, [XOp (XMult, [XVar v; num_constant_expr c]); acc]))
             (num_constant_expr x#get_n) factors) in
      XOp (XGe, [xpr; zero_constant_expr])) s#get_s

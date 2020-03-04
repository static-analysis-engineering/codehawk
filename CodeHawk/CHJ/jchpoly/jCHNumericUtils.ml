(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

open Printf

(* chlib *)
open CHBounds
open CHIntervals
open CHLanguage
open CHPretty
open CHUtils
open CHNumerical

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHJTerm

(* jchpre *)
open JCHFunctionSummary
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

let dbg = ref false 

let get_constants (jproc_info:JCHProcInfo.jproc_info_t) = 
  let var_to_const = ref [] in
  let add_const (var: variable_t) = 
    if JCHSystemUtils.is_return var then
      () 
    else 
      let jvar_info = jproc_info#get_jvar_info var in
      match jvar_info#get_constant with 
      |	Some n -> var_to_const := (var#getIndex, n) :: !var_to_const
      |	_ -> () in
  begin
    List.iter add_const jproc_info#get_variables ;    
    !var_to_const
  end
  
let mk_var_to_index (vars:variable_t list) = 
  let counter = ref (-1) in
  List.map (fun v -> incr counter; (v#getIndex, !counter)) vars 

let pp_var_to_index (var_to_index:(int * int) list) = 
  pretty_print_list
    var_to_index
    (fun (n1, n2) -> LBLOCK [INT n1; STR " -> "; INT n2]) "{" "; " "}"

(* Makes function summary predicates for the interval of a signature variable *)
let interval_to_summary_post_predicates
      var_index
      (interval:interval_t)
      type_interval = 
  let jterm1 = JLocalVar var_index in
  let preds = ref [] in
  let min = interval#getMin in 
  (if min#equal minus_inf_bound || min#equal type_interval#getMin then
    ()
  else
    begin
      let jterm2 = JConstant (min#toNumber) in
      preds := [PostRelationalExpr (JGreaterEqual, jterm1, jterm2)] 
    end) ;
  let max = interval#getMax in
  (if max#equal CHBounds.plus_inf_bound || max#equal type_interval#getMax then
    () 
  else 
    begin
      let jterm2 = JConstant (max#toNumber) in
      preds := (PostRelationalExpr (JLessEqual, jterm1, jterm2)) :: !preds 
    end) ;
  !preds 
  
let interval_to_summary_post_predicates2
      ~(is_loc:bool)
      ~(is_lc:bool)
      ~(is_length:bool)
      ~(is_aux:bool)
      ~(is_aux_length:bool)
      ~(var_index:int)
      ~(name:string)
      ~(interval:interval_t):postcondition_predicate_t list = 
  let jterm = 
    if is_lc then
      JLoopCounter var_index 
    else if is_length then 
      JSize (JLocalVar var_index) 
    else if is_loc then
      JLocalVar var_index
    else if is_aux then
      JAuxiliaryVar name
    else if is_aux_length then
      JSize (JAuxiliaryVar name)
    else
      raise (JCHBasicTypes.JCH_failure (STR "expected type of variable")) in

  let preds = ref [] in
  begin
    (match interval#singleton with 
     | Some n -> preds := [PostRelationalExpr (JEquals, jterm, JConstant n)] 
     | _ -> 
        let min = interval#getMin in 
        let max = interval#getMax in
        if min#equal minus_inf_bound || min#equal plus_inf_bound then
          ()
        else
          preds :=
            [PostRelationalExpr (JGreaterEqual, jterm, JConstant (min#toNumber))] ;
        if max#equal minus_inf_bound || max#equal plus_inf_bound then
          ()
        else
          preds :=
            (PostRelationalExpr
               (JLessEqual, jterm, JConstant (max#toNumber))) :: !preds ) ;
    !preds
  end

(* Makes function summary predicates for the excluded values of a signature variable *)
let excluded_vals_to_summary_pre_predicates
      (arg_index:int) (vals:numerical_t list) = 
  let add_excluded_val preds vl = 
    let jterm1 = JLocalVar arg_index in
    let jterm2 = JConstant vl in
    (PreRelationalExpr (JNotEqual, jterm1, jterm2)) :: preds in
  List.fold_left add_excluded_val [] vals 

let excluded_vals_to_summary_post_predicates
      (arg_index:int) (vals:numerical_t list) = 
  let add_excluded_val preds vl = 
    let jterm1 = JLocalVar arg_index in
    let jterm2 = JConstant vl in
    (PostRelationalExpr (JNotEqual, jterm1, jterm2)) :: preds in
  List.fold_left add_excluded_val [] vals 
    
let equality_to_summary_post_predicate
      (arg_index1:int) (arg_index2:int) = 
  let jterm1 = JLocalVar arg_index1 in
  let jterm2 = JLocalVar arg_index2 in
  PostRelationalExpr (JEquals, jterm1, jterm2)

let rec has_return_expr expr = 
  match expr with 
  | JLocalVar (-1) -> true
  | JLocalVar _
  | JAuxiliaryVar _ 
  | JLoopCounter _
  | JSymbolicConstant _
  | JConstant _ -> false
  | JBoolConstant _ -> false
  | JFloatConstant _ -> false
  | JStringConstant _ -> false
  | JSize t -> has_return_expr t       (* before: differentiated between array/string length and size *)
  | JArithmeticExpr (_, t1, t2) -> has_return_expr t1 || has_return_expr t2
  | JObjectFieldValue _ -> false
  | JStaticFieldValue _ -> false
  | JPower _ -> false
  | JUninterpreted _ -> false
	

let has_return_pre_predicate (pred:precondition_predicate_t) = 
  match pred with 
  | PreRelationalExpr (_, t1, t2) -> has_return_expr t1 || has_return_expr t2
  | PreNull t 
  | PreNotNull t -> has_return_expr t
  | PreValidString (t, _) -> has_return_expr t

let pre_to_post_predicate (pred:precondition_predicate_t) = 
  match pred with 
  | PreRelationalExpr (op, t1, t2) -> PostRelationalExpr (op, t1, t2)
  | PreNull t -> PostNull
  | PreNotNull t -> PostNotNull
  | PreValidString (t, s) -> PostNull (* This is not processed further so it does not matter *)

let post_predicate_to_relational_expr (post:postcondition_predicate_t) = 
  let rec jterm_to_expr term = term in
  match post with 
  | PostRelationalExpr (op, t1, t2) -> (op, jterm_to_expr t1, jterm_to_expr t2)
  | _ ->
     pr__debug [STR "Analysis failed: programming error: ";
                STR "post_predicate_to_relational_expr expected PostRelationalExpr"; NL] ;
     raise
       (JCHAnalysisUtils.numeric_params#analysis_failed
          3 "programming error: post_predicate_to_relational_expr expected PostRelationalExpr")

let var_to_abstract_side (map:(int * int) list) (ind:int) = 
  let arg_ind = List.assoc ind map in
  let jterm  = JLocalVar arg_ind in
  NumericAbstract jterm

let postcondition_predicate_to_pretty (p:postcondition_predicate_t) = 
  match p with 
  | PostRelationalExpr (op, t1, t2) ->
     LBLOCK [ jterm_to_pretty t1 ;
              STR (relational_op_to_string op) ; jterm_to_pretty t2 ]
  | PostTrue -> STR "post-true"
  | PostFalse -> STR "post-false"
  | PostNewObject cn -> LBLOCK [STR "new-object "; cn#toPretty]
  | PostObjectClass cn -> LBLOCK [ STR "class-object" ; cn#toPretty ]
  | PostNull -> STR "post-null"
  | PostNotNull -> STR "post-not-null"
  | PostElement t -> LBLOCK [STR "post "; jterm_to_pretty t] 
  | PostEmptyCollection -> STR "post-empty-collection"
  | PostSameCollection t -> LBLOCK [STR "post-same "; jterm_to_pretty t] 
  | PostWrapped t -> LBLOCK [STR "post-wrapped "; jterm_to_pretty t]
  | PostUnwrapped -> STR "post-unwrapped"
  | PostValidString s -> STR ("post-valid-string "^s)

let get_loop_counter_bounds
      (rel_exprs:relational_expr_t list) (first_pc:int) =
  let lbounds = ref [] in
  let ubounds = ref [] in
  
  let rec get_bound (jterm:jterm_t) = 
    match jterm with 
    | JLoopCounter i -> 
       if i = first_pc then
         (Some numerical_one, None)
       else
         (None, Some jterm)
    | JArithmeticExpr (JTimes, JLoopCounter i, JConstant num) 
    | JArithmeticExpr (JTimes, JConstant num, JLoopCounter i) -> 
	if i = first_pc then (Some num, None)
	else (None, Some jterm)
    | JArithmeticExpr (op, t1, t2) -> 
       let (coeff_opt1, rest_opt1) = get_bound t1 in
       let (coeff_opt2, rest_opt2) = get_bound t2 in
       let coeff_opt = 
	 match (coeff_opt1, coeff_opt2) with 
	 | (Some num, _) 
	   | (_, Some num) -> Some num
	 | _ -> None in
       let rest_opt = 
	 match (rest_opt1, rest_opt2) with 
	 | (Some rest1, Some rest2) -> Some (JArithmeticExpr (op, rest1, rest2))
	 | (Some rest, _) 
	   | (_, Some rest) -> Some rest
	 | _ -> None in
       (coeff_opt, rest_opt)
    | _ -> (None, Some jterm) in

  let rec change_signs jt = 
    match jt with 
    | JArithmeticExpr (JTimes, JConstant num, jt1) -> 
	let num_neg = num#neg in
	if num_neg#equal numerical_one then
          jt1
	else
          JArithmeticExpr (JTimes, JConstant num_neg, jt1)
    | JArithmeticExpr (JDivide, jt, JConstant num) ->
	JArithmeticExpr (JDivide, change_signs jt, JConstant num) 
    | JArithmeticExpr (op, t1, t2) -> JArithmeticExpr (op, change_signs t1, change_signs t2)
    | JConstant num -> JConstant num#neg
    | _ -> jt in

  let add_rel_expr re =
    match re with 
    | (JEquals, JLoopCounter i, jterm) ->
	if i = first_pc then
	  begin
	    lbounds := jterm :: !lbounds ;
	    ubounds := jterm :: !ubounds
	  end
    | (JLessEqual, JLoopCounter i, jterm) -> 
	if i = first_pc then
	  begin
	    ubounds := jterm :: !ubounds
	  end
    | (JGreaterEqual, JLoopCounter i, jterm) ->
	if i = first_pc then
	  begin
	    lbounds := jterm :: !lbounds
	  end	
    | (JEquals, jterm, _) -> 
       let bound = 
	 match get_bound jterm with 
	 | (Some num, None) -> JConstant numerical_zero
	 | (Some num, Some rest) ->
	    let abs_num = num#abs in
	    let bound =
	      if abs_num#equal numerical_one then
                rest
	      else
                JArithmeticExpr (JDivide, rest, JConstant abs_num) in
	    if num#gt numerical_zero then
              change_signs bound
	    else
              bound
         | _ ->
            raise (JCH_failure (STR "Error in add_rel_expr")) in
       begin
	 lbounds := bound :: !lbounds ;
	 ubounds := bound :: !ubounds
       end
    | (JGreaterEqual, jterm, _) -> (* from poly; assumes the second jterm = 0 *) 
	begin
	  match get_bound jterm with
	  | (Some num, None) ->
	      lbounds := (JConstant numerical_zero) :: !lbounds
	  | (Some num, Some rest) ->
	      let abs_num = num#abs in
	      let bound =
		if abs_num#equal numerical_one then
                  rest
		else
                  JArithmeticExpr (JDivide, rest, JConstant abs_num) in
	      if num#gt numerical_zero then
		lbounds := (change_signs bound) :: !lbounds
	      else
		ubounds := bound :: !ubounds
	  | _ -> ()
	end
    | _ -> () in
  let add_rel_expr_no_exc re =
    try add_rel_expr re with _ -> () in
  begin
    List.iter add_rel_expr_no_exc rel_exprs ;
    (!lbounds, !ubounds)
  end
  
(* It assumes jterm is a sum of products *)
let get_bound target_jterm jterm = 
  let rec get_bound jterm = 
    match jterm with
    | JAuxiliaryVar _
    | JSymbolicConstant _
    | JLocalVar _
    | JLoopCounter _
    | JSize _ -> 
	if jterm_compare jterm target_jterm = 0 then
	  (Some numerical_one, None)
	else
          (None, Some jterm)
    | JArithmeticExpr (JTimes, JConstant num, j) ->
       if (jterm_compare j target_jterm = 0) then
         (Some num, None)
       else
         (None, Some jterm)
    | JArithmeticExpr (op, t1, t2) -> 
       let (coeff_opt1, rest_opt1) = get_bound t1 in
       let (coeff_opt2, rest_opt2) = get_bound t2 in
       let coeff_opt = 
	 match (coeff_opt1, coeff_opt2) with 
	 | (Some num, _) 
	   | (_, Some num) -> Some num
	 | _ -> None in
       let rest_opt = 
	 match (rest_opt1, rest_opt2) with 
	 | (Some rest1, Some rest2) -> Some (JArithmeticExpr (op, rest1, rest2))
	 | (Some rest, _) 
	   | (_, Some rest) -> Some rest
	 | _ -> None in
       (coeff_opt, rest_opt)
    (* TBA: JPower (t,n)  ?? *)
    | _ -> (None, Some jterm) in
  
  match get_bound jterm with 
  | (Some num, None) ->
      if num#gt numerical_zero then
	(Some (JConstant numerical_zero), None)
      else
        (None, Some (JConstant numerical_zero))
  | (Some num, Some rest) -> 
      let rec change_signs jt = 
	match jt with
        (* TBA: JPower (t,n) ?? *)
	| JArithmeticExpr (JTimes, JConstant num, jt1) -> 
	    let num_neg = num#neg in
	    if num_neg#equal numerical_one then
              jt1
	    else
              JArithmeticExpr (JTimes, JConstant num_neg, jt1)
	| JArithmeticExpr (op, t1, t2) ->
           JArithmeticExpr (op, change_signs t1, change_signs t2)
	| JConstant num -> JConstant num#neg
	| _ -> jt in
      if num#gt numerical_zero then 
	let changed_rest = change_signs rest in
	if num#equal numerical_one then
          (Some changed_rest, None)
	else
          (Some (JArithmeticExpr (JDivide, changed_rest, JConstant num)), None)
      else
	if num#equal numerical_one#neg then
          (None, Some rest)
	else
          (None, Some (JArithmeticExpr (JDivide, rest, JConstant num#neg)))
  | _ -> (None, None)
	
let get_bounds target_jterm rel_exprs =
  let lbounds = ref [] in
  let ubounds = ref [] in
  let add_rel_expr re =
    match re with 
    | (JEquals, jterm1, jterm2) ->
	if jterm_compare jterm1 target_jterm = 0 then
	  begin
	    lbounds := jterm2 :: !lbounds ;
	    ubounds := jterm2 :: !ubounds
	  end
	else
	  begin
	    match get_bound target_jterm jterm1 with (* from poly; assumes the second jterm = 0 *) 
	    | (Some bound, _) 
	    | (_, Some bound) ->
		lbounds := bound :: !lbounds ;
		ubounds := bound :: !ubounds
	    | _ -> ()
	  end
    | (JLessEqual, jterm1, jterm2) ->
	if jterm_compare jterm1 target_jterm = 0 then
	  ubounds := jterm2 :: !ubounds 
    | (JGreaterEqual, jterm1, jterm2) ->  (* from interval *)
	if jterm_compare jterm1 target_jterm = 0 then
	  lbounds := jterm2 :: !lbounds
	else (* from poly; assumes the second jterm = 0 *) 
	  begin
	    match get_bound target_jterm jterm2 with 
	    | (Some bound, _) -> 
		lbounds := bound :: !lbounds
	    | (_, Some bound) ->
		ubounds := bound :: !ubounds
	    | _ -> ()
	  end
    | _ -> () in
  begin
    List.iter add_rel_expr rel_exprs ;
    (!lbounds, !ubounds)
  end
  
(* Assumes linear jterm *)
let rec negate_jterm jterm =
  match jterm with
  (* TBA: JPower (t,n) ?? *)
  | JConstant n -> JConstant n#neg
  | JArithmeticExpr (JTimes, JConstant c, jterm) ->
      JArithmeticExpr (JTimes, JConstant c#neg, jterm) 
  | JArithmeticExpr (JTimes, jterm, JConstant c) ->
      JArithmeticExpr (JTimes, jterm, JConstant c#neg)
  | JArithmeticExpr (JPlus, jterm1, jterm2) -> 
      JArithmeticExpr (JPlus, negate_jterm jterm1, negate_jterm jterm2)
  | JArithmeticExpr (JMinus, jterm1, jterm2) -> 
      JArithmeticExpr (JMinus, negate_jterm jterm1, negate_jterm jterm2)
  | JLocalVar _ 
  | JAuxiliaryVar _
  | JSymbolicConstant _ 
  | JLoopCounter _ 
  | JSize _ -> 
     JArithmeticExpr (JTimes, JConstant (numerical_one#neg), jterm)
  | _ -> jterm


(* gets vars and length of vars *)	
let get_jterm_vars jterm =
  let rec get_vars vars jterm = 
    match jterm with
    | JLocalVar _ 
    | JAuxiliaryVar _
    | JSymbolicConstant _
    | JLoopCounter _ 
    | JSize _ -> jterm :: vars
    | JArithmeticExpr (_, jterm1, jterm2) ->
	get_vars (get_vars vars jterm1) jterm2
    | _ -> vars in
  get_vars [] jterm

let get_field_term (cmsix:int) (fInfo:field_info_int) =
  let cnix = fInfo#get_class_name#index in
  let field_name = fInfo#get_class_signature#name in
  if fInfo#is_static then
    JStaticFieldValue (cnix, field_name)
  else
    JObjectFieldValue (cmsix, -1, cnix, field_name) 
  
    
let change_to_fields
      (cmsix:int)
      (var_to_field:(variable_t * field_info_int) list)
      (post:postcondition_predicate_t) = 
  let get_field_term str =
    let ind = int_of_string (String.sub str 4 ((String.length str) - 4)) in
    let is_var (var, _) = var#getIndex = ind in
    let (var, field_info) = List.find is_var var_to_field in
    let field_term = get_field_term cmsix field_info in
    let term = 
      if JCHSystemUtils.is_length var then
        JSize field_term
      else
        field_term in
    term in
  let rec change_jterm jterm = 
    match jterm with
    | JAuxiliaryVar str ->
	begin
	  try
	    get_field_term str 
	  with _ -> jterm
	end
    | JSize jterm ->
	begin
	  JSize (change_jterm jterm)
	end
    | JArithmeticExpr (op, jterm1, jterm2) ->
	JArithmeticExpr (op, change_jterm jterm1, change_jterm jterm2)
    | _ -> jterm in

  let change_post pred =
    match pred with
    | PostRelationalExpr (op, jterm1, jterm2) ->
	PostRelationalExpr (op, change_jterm jterm1, change_jterm jterm2)
    | _ -> pred in

  change_post post
    

let is_numeric (fInfo:field_info_int) =
  let cfs = fInfo#get_class_signature in
  let fs = cfs#field_signature in
  let t = fs#descriptor in
  match t with
  | TBasic Int
  | TBasic Short
  | TBasic Char
  | TBasic Byte
  | TBasic Long
  | TBasic Float
  | TBasic Double -> true
  | TBasic _ -> false
  | TObject TClass cn -> 
      begin
	match cn#name with 
	| "java.lang.Integer"
	| "java.lang.Short" 
	| "java.lang.Character"
	| "java.lang.Byte" 
	| "java.lang.Long"
	| "java.lang.Float"
	| "java.lang.Double"
	| "java.math.BigInteger"
	| "java.math.BigDecimal" -> true
	| _ -> false
      end
  | TObject (TArray _) -> false

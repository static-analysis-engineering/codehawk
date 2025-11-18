(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2025 Aarno Labs LLC

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
open CHNestedCommands

(* xprlib *)
open Xprt
open XprTypes
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHExternalPredicate
open CCHFileContract
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchanalyze *)
open CCHAnalysisTypes
open CCHCommand

let p2s = CHPrettyUtil.pretty_to_string


class num_assignment_translator_t
  (env:c_environment_int)
  (exp_translator:exp_translator_int):assignment_translator_int =
object (self)

  val fdecls = env#get_fdecls
  val mutable context = mk_program_context ()
  val mutable location = unknown_location

  method translate (ctxt:program_context_int) (loc:location) (lhs:lval) (rhs:exp) =
    let _ = context <- ctxt in
    let _ = location <- loc in
    if self#has_contract_instr loc.line lhs then
      self#do_contract_instr loc.line context lhs
    else
      try
        let chifVar = exp_translator#translate_lhs context lhs in
        let tmpProvider = fun () -> env#mk_num_temp in
        let cstProvider = fun (n:numerical_t) -> env#mk_num_constant n in
        let rhsExpr = exp_translator#translate_exp context rhs in
        let (rhsCode,numExp) = xpr2numexpr tmpProvider cstProvider rhsExpr in
        let assign =
	  if chifVar#isTmp then
            let memoryvars = env#get_memory_variables in
            let _ =
              log_diagnostics_result
                ~tag:"abstract memory variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                (List.map (fun v -> (p2s v#toPretty)) memoryvars) in
            CCMD (ABSTRACT_VARS memoryvars)
	  else if env#has_constant_offset chifVar then
	    make_c_cmd (ASSIGN_NUM (chifVar, numExp))
          else
            let memoryvars = env#get_memory_variables_with_base chifVar in
            let _ =
              log_diagnostics_result
                ~tag:"abstract memory variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                (List.map (fun v -> (p2s v#toPretty)) memoryvars) in
            CCMD (ABSTRACT_VARS memoryvars) in
        [rhsCode; assign]
      with
      | CCHFailure p ->
         raise (CCHFailure
	          (LBLOCK [
                       STR "Error in translating assignment ";
		       lval_to_pretty lhs;
                       STR " := ";
                       exp_to_pretty rhs;
		       STR ": ";
                       p]))

  method private has_contract_instr (line:int) (lhs:lval)  =
    file_contract#has_function_contract env#get_functionname
    && (file_contract#get_function_contract env#get_functionname)#has_instrs line
    && (let fcontract = file_contract#get_function_contract env#get_functionname in
        let instrs = fcontract#get_instrs line in
        match instrs with
        | [SetVar (_, clhs, _crhs)] ->
           (match (clhs,lhs) with
            | (LocalVariable lvar, (Var (vname, _), NoOffset)) -> lvar = vname
            | _ -> false)
        | _ -> false)

  method private do_contract_instr
                   (line:int) (context:program_context_int) (lhs:lval) =
    if self#has_contract_instr line lhs then
      let tmpProvider = fun () -> env#mk_num_temp in
      let cstProvider = fun (n:numerical_t) -> env#mk_num_constant n in
      let fcontract = file_contract#get_function_contract env#get_functionname in
      let instrs = fcontract#get_instrs line in
      match instrs with
      | [SetVar (_, clhs, crhs)] ->
         let tmp = env#mk_num_temp in
         begin
           match (clhs,lhs) with
           | (LocalVariable lvar, (Var (vname,_), NoOffset)) when vname = lvar ->
              let chifVar = exp_translator#translate_lhs context lhs in
              let (rhscode, _rhs) =
                let get_assert x =
                  let (code, bExp) = xpr2boolexpr tmpProvider cstProvider x in
                  [code; make_c_cmd (make_assert bExp)] in
                begin
                  match crhs  with
                  | ChoiceValue (Some (NumConstant lb), Some (NumConstant ub)) ->
                     let lbx = XOp (XGe, [XVar tmp; num_constant_expr lb]) in
                     let ubx = XOp (XLe, [XVar tmp; num_constant_expr ub]) in
                     (((get_assert lbx) @ (get_assert ubx)), tmp)
                  | _ ->
                     raise
                       (CCHFailure
                          (LBLOCK [STR "contract instruction rhs not recognized"]))
                end in
              rhscode @ [(make_c_cmd (ASSIGN_NUM (chifVar, NUM_VAR tmp)))]
           | _ ->
              raise
                (CCHFailure
                   (LBLOCK [
                        STR "Use of of contract instruction with unknown ";
                        STR "instruction: ";
                        STR "lhs: ";
                        lval_to_pretty lhs;
                        STR "clhs: ";
                        s_term_to_pretty clhs]))
         end
      | _ ->
         raise
           (CCHFailure
              (LBLOCK [STR "Use of contract instruction not recognized"]))
    else
      raise
        (CCHFailure (LBLOCK [STR "Not a contract instruction"]))

  method private make_non_negative_assert (v:variable_t) =
    let tmpProvider = (fun () -> env#mk_num_temp) in
    let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
    let x = XOp (XGe, [XVar v; zero_constant_expr]) in
    let (_code, bExp) = xpr2boolexpr tmpProvider cstProvider x in
    make_c_cmd (make_assert bExp)

end


class sym_assignment_translator_t
  (env:c_environment_int)
  (exp_translator:exp_translator_int):assignment_translator_int =
object (self)

  val fdecls = env#get_fdecls

  method private get_function_pointer rhs =
    match type_of_exp fdecls rhs with
    | TPtr (TFun _, []) ->
      begin
	match rhs with
	| AddrOf (Var (fname, fvid), NoOffset) -> Some (fname, fvid)
	| _ -> None
      end
    | _ -> None

  method translate
           (context:program_context_int) (loc:location) (lhs:lval) (rhs:exp) =
    let chifVar = exp_translator#translate_lhs context lhs in
    let atts = match type_of_lval fdecls lhs with
      | TPtr _ ->
	if is_field_lval_exp rhs then
	  let (fname,ckey) = get_field_lval_exp rhs in
	  ["field"; fname; string_of_int ckey]
	else
	  begin
	    match rhs with
	    | Lval (Var (vname,vid),NoOffset) ->
	      let vinfo = env#get_varinfo vid in
	      if vinfo.vglob then
		["global"; vname; string_of_int vid]
	      else
		[]
            | BinOp ((IndexPI | PlusPI | MinusPI), _, _, _) ->
               ["c"]
	    | _ -> []
	  end
      | _ -> [] in
    let atts = match self#get_function_pointer rhs with
      | Some (fname,fvid) -> atts @ ["fptr"; fname; string_of_int fvid]
      | _ -> atts in
    let sym = new symbol_t ~atts ("assignedAt#" ^ (string_of_int loc.line)) in
    [make_c_cmd (ASSIGN_SYM (chifVar, SYM sym))]

end

class sym_pointersets_assignment_translator_t
        (env:c_environment_int)
        (exp_translator:exp_translator_int):assignment_translator_int =
object (self)

  val fdecls = env#get_fdecls

  method private dmsg (ctxt: program_context_int) (loc: location): string =
    env#get_functionname ^ ":"
    ^ (ctxt#to_string)
    ^ " (line: " ^ (string_of_int loc.line) ^ ")"

  method translate
           (context:program_context_int) (loc:location) (lhs:lval) (rhs:exp) =
    try
      let chifVar = exp_translator#translate_lhs context lhs in
      let rhsExpr = exp_translator#translate_exp context rhs in
      let assign =
        if chifVar#isTmp then
          if is_pointer_type (type_of_lval fdecls lhs) then
            let ptrvars = env#get_pointer_variables SYM_VAR_TYPE in
            let _ =
              log_diagnostics_result
                ~tag:"abstract pointer variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                (List.map (fun v -> p2s v#toPretty) ptrvars) in
            make_c_cmd (ABSTRACT_VARS ptrvars)
          else
            make_c_cmd SKIP
        else if is_pointer_type (type_of_lval fdecls lhs) then
          match rhsExpr with
          | XConst (SymSet []) -> (make_c_cmd SKIP)
          | XConst (SymSet [sym]) -> make_c_cmd (ASSIGN_SYM (chifVar, SYM sym))
          | XConst (SymSet lst) ->
             make_c_branch
               (List.map (fun s -> [make_c_cmd (ASSIGN_SYM (chifVar, SYM s))]) lst)
          | XVar v -> make_c_cmd (ASSIGN_SYM (chifVar, SYM_VAR v))
          | _ -> make_c_cmd (ASSIGN_SYM (chifVar, SYM (new symbol_t "unknown")))
        else
          make_c_cmd SKIP in
      let _ =
        log_diagnostics_result
          ~msg:(self#dmsg context loc)
          ~tag:"sym_pointersets:translate assignment"
          __FILE__ __LINE__
          ["lhs: " ^ (p2s (lval_to_pretty lhs));
           "rhs: " ^ (p2s (exp_to_pretty rhs));
           "result: " ^ (p2s (c_cmd_to_pretty assign))] in
      [assign]
    with
    | CCHFailure p ->
       begin
         ch_error_log#add
           "sym-pointer assignment"
           (LBLOCK [
                lval_to_pretty lhs;
                STR " := " ;
                exp_to_pretty rhs;
                STR "; leads to: ";
                p]);
         raise (CCHFailure p)
       end

end


class sym_statesets_assignment_translator_t
        (env:c_environment_int)
        (exp_translator:exp_translator_int):assignment_translator_int =
object

  val fdecls = env#get_fdecls

  method translate
           (context:program_context_int) (_loc:location) (lhs:lval) (rhs:exp) =
    let chifVar = exp_translator#translate_lhs context lhs in
    let rhsExpr = exp_translator#translate_exp context rhs in
    let assign =
      if chifVar#isTmp then
        make_c_cmd SKIP
      else
        match rhsExpr with
        | XVar v -> make_c_cmd (ASSIGN_SYM (chifVar, SYM_VAR v))
        | _ -> make_c_cmd SKIP in
    [assign]

end


let get_num_assignment_translator = new num_assignment_translator_t

let get_sym_assignment_translator = new sym_assignment_translator_t

let get_sym_pointersets_assignment_translator =
  new sym_pointersets_assignment_translator_t

let get_statesets_assignment_translator =
  new sym_statesets_assignment_translator_t

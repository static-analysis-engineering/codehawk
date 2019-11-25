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
open CHOnlineCodeSet

(* chutil *)
open CHLogger
open CHNestedCommands
open CHPrettyUtil

(* xprlib *)
open XprTypes
open XprToPretty

(* cchlib *)
open CCHAnalysisTypes
open CCHExpr
open CCHUtilities

module EU = CCHEngineUtil

let rec c_cmd_to_pretty c =
  match c with
  | CNOP -> STR "CNOP"
  | CCMD c ->
    LBLOCK [ STR "CCMD " ; command_to_pretty 0 c ]
  | CBLOCK l ->
    let lp = list_to_pretty (fun c -> c_cmd_to_pretty c) NL l in
    LBLOCK [ STR "CBLOCK" ; NL ; INDENT (2, lp) ; NL ]
      

let make_c_nop = make_nested_nop
let make_c_cmd = make_nested_cmd
let make_c_cmd_block = make_nested_cmd_block

let make_operation name op_id vars =
  let op_name = EU.numbersymbol op_id name in
  let op_args = List.map (fun v -> (EU.variable2string v, v, READ)) vars in
  let op = { op_name = op_name ; op_args = op_args } in
    make_c_cmd ( OPERATION op )

let rec is_c_nop ccmd =
  match ccmd with
  | CNOP -> true
  | CBLOCK l -> List.fold_left (fun a c -> a && (is_c_nop c)) true l
  | _ -> false
    
let flatten = flatten

let flatten_nested_cmd_list = flatten_nested_cmd_list

let ccmds2cmds = nested_cmds_2_cmds

let ccmd2cmds = nested_cmd_2_cmds

let ccmd2cmd (ccmd:c_cmd_t):cmd_t = match ccmd with CCMD cmd -> cmd | _ ->
  begin
    ch_error_log#add "invocation error" (STR "Problem with flattening cmd list") ;
    raise (CCHFailure (STR "CCommand.ccmd2cmd"))
  end

let filter_out_skips (l:cmd_t list):cmd_t list =
  List.filter (fun c -> match c with SKIP -> false | _ -> true) l

let make_transaction (sym:symbol_t) (tmps_requested:bool) (ccmds:nested_cmd_t list):cmd_t =
  let cmds = filter_out_skips (ccmds2cmds ccmds) in
    match cmds with
    | [] -> SKIP
    | [cmd] -> 
      if tmps_requested
      then
	TRANSACTION (sym, EU.mkCode cmds, None)
      else
	cmd
    | _ -> TRANSACTION (sym, EU.mkCode cmds, None)

let make_labeled_transaction 
    (stmt_id:int) (tmps_requested:bool) (ccmds:nested_cmd_t list):cmd_t =
  make_transaction (EU.symbol ("stmt_" ^ (string_of_int stmt_id))) tmps_requested ccmds

let make_command (sym:symbol_t) (cmds:cmd_t list):cmd_t =
  let l = filter_out_skips cmds in
  match l with
  |  [] -> SKIP
  | [cmd] -> cmd
  | _ -> CODE (sym, EU.mkCode l)
    
let make_c_branch (ccmd_lists:(nested_cmd_t list list)):nested_cmd_t =
  match ccmd_lists with
  | [] -> make_c_nop ()
  | [lst] -> make_c_cmd_block lst
  | _ ->
    let flat_lists = List.map flatten_nested_cmd_list ccmd_lists in
    let code_lists = List.map (fun l -> EU.mkCode (ccmds2cmds l)) flat_lists in
    make_c_cmd (BRANCH code_lists)
      
let make_labeled_command (stmt_id:int) (cmds:cmd_t list):cmd_t =
  make_command (EU.symbol ("stmt_" ^ (string_of_int stmt_id))) cmds

let make_call (name:string) (bindings:bindings_t) =
  CALL (EU.symbol name, bindings)

let make_nop () = SKIP

let make_assert (b:boolean_exp_t) = ASSERT b

let make_branch (cmd_lists:cmd_t list list):cmd_t =
  BRANCH (List.map EU.mkCode (List.map filter_out_skips cmd_lists))

let make_loop (when_cond:cmd_t list) (exit_cond:cmd_t list) (body:cmd_t list):cmd_t =
  let when_c = filter_out_skips when_cond in
  let exit_c = filter_out_skips exit_cond in
  let body_c = filter_out_skips body in
    LOOP (EU.mkCode when_c, EU.mkCode exit_c, EU.mkCode body_c)

let make_break (name:string) = BREAK (EU.symbol name)

let make_breakout_block (name:string) (cmds: cmd_t list):cmd_t =
  BREAKOUT_BLOCK (EU.symbol name, EU.mkCode (filter_out_skips cmds))

let make_abstract_vars (vars:variable_t list) = ABSTRACT_VARS vars

let make_symbolic_assign (var:variable_t) (expr:xpr_t):c_cmd_t =
  match expr with
  | XVar v -> make_c_cmd (ASSIGN_SYM (var, SYM_VAR v))
  | XConst (SymSet [s]) -> make_c_cmd (ASSIGN_SYM (var, SYM s))
  | XConst (SymSet l) ->
    let assigns = 
      List.map (fun s -> [ make_c_cmd (ASSIGN_SYM (var, SYM s)) ]) l in
    make_c_branch assigns
  | _ ->
    begin
      chlog#add "unknown symbolic assign"
	(LBLOCK [ xpr_formatter#pr_expr expr ]) ;
      make_c_branch
	[ [ make_c_cmd (ASSIGN_SYM (var, SYM null_symbol)) ] ;
	  [ make_c_cmd (ASSIGN_SYM (var, SYM unknown_address_symbol)) ] ]
    end

let insert_symbols (vars:variable_t list) (syms:symbol_t list) =
  let branches =
    List.map (fun s ->
        List.map (fun v -> make_c_cmd (ASSIGN_SYM (v, SYM s))) vars) syms in
  let branches = [ make_c_cmd SKIP ] :: branches in
  make_c_branch branches
  
        

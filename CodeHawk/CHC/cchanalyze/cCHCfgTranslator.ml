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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprToPretty
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHDictionary
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchanalyze *)
open CCHAnalysisTypes
open CCHAssignmentTranslator
open CCHCallTranslator
open CCHCommand
open CCHControlFlowGraph
open CCHEnvironment
open CCHExpTranslator
open CCHOperationsProvider

module EU = CCHEngineUtil
module H = Hashtbl

let x2p = xpr_formatter#pr_expr
let cd = CCHDictionary.cdictionary
	
class cfg_translator_t 
  (env:c_environment_int) 
  (assignment_translator:assignment_translator_int)
  (call_translator:call_translator_int)
  (exp_translator:exp_translator_int)
  (ops_provider:operations_provider_int):cfg_translator_int =
object (self)
  
  method translate_breakout_block block gotos context =
    let cmdList = self#translate_block block gotos context in
    let cmd = make_breakout_block env#get_function_break_label cmdList in
    [ cmd ]
      
  method translate_cfg_breakout_block block gotos context =
    if List.length block.bstmts > 0 then
      let stmts = List.rev (List.tl (List.rev block.bstmts)) in
      let lastStmt = List.hd (List.rev block.bstmts) in
      let cfgCmd = self#translate_unstructured_stmt_group stmts gotos context in
      let lastCmd = self#translate_stmt lastStmt gotos (context#add_stmt lastStmt.sid) in
      let cmd = make_breakout_block env#get_function_break_label [ cfgCmd ; lastCmd ] in
      [ cmd ]
    else
      [ SKIP ]
      
  method private translate_unstructured_stmt_group stmts gotos context =
    if List.length stmts = 0 then SKIP else
      let firstStmt = List.hd stmts in
      let _ = env#set_current_stmt_id firstStmt.sid in
      let sym = env#get_current_stmt_id_label in
      let edges = ref [] in
      let addEdge s d = edges := (s,d) :: !edges in
      let entryLabel = EU.numbersymbol firstStmt.sid "entry" in
      let exitLabel = EU.numbersymbol firstStmt.sid "exit" in
      let entryState = EU.mkState entryLabel [] in
      let exitState = EU.mkState exitLabel [] in
      let cfg = EU.mkCFG entryState exitState in
      let descendants = List.concat (List.map get_descendants stmts) in
      let successors stmt =
        List.map (fun sid ->
            if List.mem sid descendants then EU.numbersymbol sid "stmt" else exitLabel)
                 stmt.succs in
    
      let rec aux stmt context =
        let _ = env#set_current_stmt_id stmt.sid in
        let sym = env#get_current_stmt_id_label in
        let vacuousState = EU.mkState sym [] in 
        match stmt.skind with
	  
        | Instr l ->
	   let cmd = self#translate_instr_list l context in
	   let state = EU.mkState sym [ cmd ] in
	   begin
	     cfg#addState state ;
	     List.iter (fun s -> addEdge sym s) (successors stmt)
	   end
	   
        | Return (e,loc) ->
	   let cmd = self#translate_return_stmt e loc context#add_return in
	   let state = EU.mkState sym [ cmd ] in
	   begin
	     cfg#addState state ;
	     match successors stmt with 
	     | [] -> addEdge sym exitLabel
	     | _ -> List.iter (fun s -> addEdge sym s) (successors stmt)
	   end
	   
        | Goto (_,loc)
          | Break loc
          | Continue loc ->
	   begin
	     cfg#addState vacuousState ;
	     env#set_current_location loc ;
	     List.iter (fun s -> addEdge sym s) (successors stmt)
	   end
	  
        | If (cond, t, e, loc) ->
	   let _ = env#set_current_location loc in
	   let ops = ops_provider#get_cmd_operations context#add_if_expr in
	   let (thenC,elseC) = exp_translator#translate_condition context#add_if_expr cond in
	   let succs = successors stmt in
	   begin
	     match succs with
	     | [] -> raise (CCHFailure
                              (LBLOCK [ STR "Structural_error: If statement without successor at " ;
					STR "(" ; STR loc.file ; STR "," ; INT loc.line ; STR ")" ]))
	     | [s] ->
	        let preState = EU.mkState sym ops in
	        begin
	          cfg#addState preState ;
	          addEdge sym s ;
	          aux_list t.bstmts context#add_if_then ;
	          aux_list e.bstmts context#add_if_else ;
	        end
	     | _ ->
	        let trueSym = EU.add_to_symbol sym "_true" in
	        let falseSym = EU.add_to_symbol sym "_false" in
	        let preState = EU.mkState sym ops in
	        let trueState = EU.mkState trueSym [ thenC ] in
	        let falseState = EU.mkState falseSym [ elseC ] in
	        begin
	          cfg#addState preState ;
	          cfg#addState trueState ;
	          cfg#addState falseState ;
	          addEdge sym trueSym ;
	          addEdge sym falseSym ;
	          addEdge trueSym (List.nth succs 0) ;
	          addEdge falseSym (List.nth succs 1) ;
	          aux_list t.bstmts context#add_if_then ;
	          aux_list e.bstmts context#add_if_else
	        end
	   end
	   
        | Loop (b, loc, _, _) ->
	   begin
	     env#set_current_location loc ;
	     cfg#addState vacuousState ;
	     List.iter (fun s -> addEdge sym s) (successors stmt) ;
	     aux_list b.bstmts context#add_loop
	   end
	  
        | Switch (_, b, _, loc) ->
	   begin
	     env#set_current_location loc ;
	     cfg#addState vacuousState ;
	     List.iter (fun s -> addEdge sym s) (successors stmt) ;
	     aux_list b.bstmts context
	   end
	  
        | _ ->
	   raise (CCHFailure
                    (LBLOCK [ STR "Structural_error: Unrecognized statement type" ]))
	  
      and aux_list l context = List.iter (fun s -> aux s (context#add_stmt s.sid)) l in
      
      begin
        cfg#addStates [ entryState ; exitState ] ;
        aux firstStmt (context#add_stmt firstStmt.sid) ;
        aux_list (List.tl stmts) context ;
        cfg#addEdge entryLabel (EU.numbersymbol firstStmt.sid "stmt") ;
        List.iter (fun (s,d) -> cfg#addEdge s d) !edges ;
        CFG (sym,cfg)
      end
      
  method private translate_switch (controlExp:exp) (stmts:stmt list) gotos context =
    let stmtId = env#get_current_stmt_id in
    let ops = ops_provider#get_cmd_operations context#add_switch_expr in
    let tmpProvider = (fun () -> env#mk_num_temp) in
    let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
    let make_assume x =
      let trivial b = match b with TRUE | RANDOM -> true | _ -> false in
      let (code,bExp) = xpr2boolexpr tmpProvider cstProvider x in
      let assume =
        if trivial bExp then
          make_c_nop ()
        else
          make_c_cmd (make_assert bExp) in
      make_c_cmd_block [ code ; assume ] in
    let make_exp_assume b =
      let rec aux e =
	match e with
	| BinOp (LAnd, l, r, _) -> make_c_cmd_block [ aux l ; aux r ]
	| _ ->
           make_assume (exp_translator#translate_exp context#add_switch_expr e) in 
      aux b in
    let get_case_exprs labels =
      List.fold_right (fun lab a ->
	match lab with
	| Case (exp,_) -> exp :: a
	| _ -> a) labels [] in
    let caseExprs =
      List.fold_right (fun stmt a -> (get_case_exprs stmt.labels) @ a) stmts [] in
    let is_case_label = function Case _ -> true | _ -> false in
    let is_default_label = function Default _ -> true | _ -> false in
    let is_break_stmt stmt = match stmt with Break _ -> true | _ -> false in
    let defaultExpr =
      match caseExprs with
      | [] -> one    (* zero ?? *)
      | [ e ] -> mk_disequality controlExp e     (* e ??? *)
      | h::tl ->
	let hd = mk_disequality controlExp h in
	List.fold_right (fun e a -> 
	  let ed = mk_disequality controlExp e in mk_logical_and ed a) tl hd in
    let has_label stmt = List.exists (fun l -> 
      is_case_label l || is_default_label l) stmt.labels in
    let get_label_exprs stmt =
      List.fold_right (fun l a ->
	match l with
	| Case (e,_) -> (mk_equality controlExp e) :: a
	| Default _ -> defaultExpr :: a
	| _ -> a) stmt.labels [] in
    let make_guard (el:exp list):cmd_t =
      let _ = env#start_transaction in
      let assumes = List.map make_exp_assume el in
      let (tmps,constantAssigns) = env#end_transaction in
      let constantAssigns = List.map make_c_cmd constantAssigns in
      let tlabel = string_printer#print (pretty_print_list el exp_to_pretty "" " -- " "") in
      match assumes with
      | [] -> ASSERT FALSE
      | [ a ] -> make_transaction (new symbol_t tlabel) tmps (constantAssigns @ [a])
      | _ -> make_transaction (new symbol_t tlabel) tmps
	(constantAssigns @ [ make_c_branch (List.map (fun a -> [a]) assumes) ]) in
    let lift_branch (oldguard:cmd_t) (branch:cmd_t list) (newguard:cmd_t) (topguard:cmd_t) =
      match branch with
      | [] -> [ newguard ]
      | _ -> [ topguard ; make_branch [ branch ; [ newguard ] ] ] in
    let rec aux (closed:cmd_t list list) (current: cmd_t list) (oldLabels:exp list) (stmts:stmt list) =
      match stmts with
      | [] -> current :: closed
      | [ s ] when is_break_stmt s.skind -> [] :: current :: closed
      | s::sr when is_break_stmt s.skind -> aux (current::closed) [] [] sr
      | s::sr when has_label s ->
	begin
	  match current with
	  | [] ->
	    let labelExprs = get_label_exprs s in
	    let guard = make_guard labelExprs in
	    let c = self#translate_stmt s gotos (context#add_stmt s.sid) in
	    aux closed [ guard ; c ] labelExprs sr
	  | _ ->
	    let newLabels = get_label_exprs s in
	    let oldGuard = make_guard oldLabels in
	    let newGuard = make_guard newLabels in
	    let topGuard = make_guard (oldLabels @ newLabels) in
	    let c = self#translate_stmt s gotos (context#add_stmt s.sid) in
	    let b = lift_branch oldGuard current newGuard topGuard in
	    aux closed (b @ [c]) (newLabels @ oldLabels) sr
	end
      | s::sr ->
	let c = self#translate_stmt s gotos (context#add_stmt s.sid) in
	aux closed (current @ [c]) oldLabels sr  in
    let branches = aux [] [] [] stmts in
    make_labeled_command stmtId (ops @ [ make_branch branches])
      
  method private decompose_loop stmts gotos context =
    let (terminationTest, loopStmts,ops) =
      let rec skip_empty l =
	match l with
	| [] -> []
	| { skind = Instr [] ; labels = []} :: rest -> skip_empty rest
	| _ -> l in
      match skip_empty stmts with
      | ({ skind = If(e,tb,eb,_) ; labels = [] } as s) :: rest ->
	let ops = ops_provider#get_cmd_operations (context#add_stmt s.sid)#add_if_expr in
	begin
	  match (skip_empty tb.bstmts, skip_empty eb.bstmts) with
	  | ([], {skind = Break _ ; labels = []} :: _) ->
             (e,rest,ops)
	  | ({skind = Break _ ; labels = []} :: _, []) ->
             (UnOp (LNot, e, TInt (IInt,[])), rest,ops)
	  | _ ->
             (Const (CInt (Int64.of_int 1,IInt,None)), stmts,ops)
	end
      | _ -> (Const (CInt (Int64.of_int 1,IInt,None)), stmts,[]) in
    let bodyStmts =
      List.map (fun s ->
          self#translate_stmt s gotos (context#add_stmt s.sid)) loopStmts in
    (terminationTest, ops, bodyStmts) 
      
      
  method private translate_stmt (stmt:stmt) gotos context =
    if gotos#is_goto_block stmt then
      self#translate_unstructured_stmt_group [ stmt ] gotos context#pop
    else
      let _ = env#set_current_stmt_id stmt.sid in
      match stmt.skind with
      | Instr l -> self#translate_instr_list l context
      | Return (e,loc) -> self#translate_return_stmt e loc context#add_return
      | If (c, t, e, loc) ->
	let stmtId = env#get_current_stmt_id in
	let _ = env#set_current_location loc in
	let (then_c,else_c) = exp_translator#translate_condition context#add_if_expr c in
	let ops = ops_provider#get_cmd_operations context#add_if_expr in
	let tb = then_c :: (self#translate_block t gotos context#add_if_then) in
	let eb = else_c :: (self#translate_block e gotos context#add_if_else) in
	make_labeled_command stmtId (ops @ [ make_branch [ tb ; eb ]])
      | Loop (body, loc, _,_) ->
	let _ = env#set_current_location loc in
	let _ = env#set_current_stmt_id stmt.sid in
	begin
	  match self#assess_loop_body body.bstmts context#add_loop with
	  | Some cmd -> cmd
	  | _ ->
	    begin 
	      let _ = env#start_loop in
	      let (termination_test,ops,loopBody) =
                self#decompose_loop body.bstmts gotos context#add_loop in
	      let (whenc, exitc) = exp_translator#translate_condition context termination_test in
	      let loopBody = make_breakout_block env#get_continue_label loopBody in
	      let loopCmd = make_loop (ops @ [ whenc ]) [ exitc ] [ loopBody ] in
	      let loopCmd = make_breakout_block env#get_break_label [ loopCmd ] in
	      let _ = env#end_loop in
	      loopCmd
	    end
	end
      | Switch (e,b,l,loc) ->
	begin
	  env#set_current_location loc ;
	  env#start_switch ;
	  let switchCmd = self#translate_switch e b.bstmts gotos context in
	  let switchCmd = make_breakout_block env#get_break_label [ switchCmd ] in
	  let _ = env#end_switch in
	  switchCmd
	end
      | Break loc ->
	begin
	  env#set_current_location loc ;
	  make_break env#get_break_label
	end
      | Continue loc ->
	begin
	  env#set_current_location loc ;
	  make_break env#get_continue_label
	end
      | Block b ->
	make_labeled_command env#get_current_stmt_id (self#translate_block b gotos context)
      | _ -> SKIP
	
  method private translate_block block gotos context =
    List.map (fun stmt -> 
      self#translate_stmt stmt gotos (context#add_stmt stmt.sid)) block.bstmts
      
  method private assess_loop_body bstmts context =
    match bstmts with
    | [ stmt1 ; stmt2 ] ->
      begin
	match (stmt1.skind, stmt2.skind) with
	| (Instr l, Break _) ->
	  begin
	    env#set_current_stmt_id stmt1.sid ;
	    Some (self#translate_instr_list l (context#add_stmt stmt1.sid))
	  end
	| _ -> None
      end
    | _ -> None

  (* TBD: expand branch conditions, see ref *)

  method private translate_return_stmt e loc context =
    let _ = env#set_current_location loc in
    let ops = ops_provider#get_cmd_operations context in
    match e with
    | Some exp ->
       let returnOps = ops_provider#get_return_operation context exp in
       begin
         env#add_return_context context ;
         make_labeled_command
           env#get_current_stmt_id 
	   (ops @ returnOps @ [ make_break env#get_function_break_label ])
       end
    | _ ->
       make_labeled_command
         env#get_current_stmt_id (ops @ [ make_break env#get_function_break_label ])
      
  method private translate_instr_list (l:instr list) context =
    let stmt_id = env#get_current_stmt_id in
    let _ = env#start_transaction in
    let ccmds =
      List.mapi (fun i instr ->
          self#translate_basic_block_cmd instr (context#add_instr i)) l in
    let (tmps_requested,constantAssigns) = env#end_transaction in
    let constantAssigns = List.map make_c_cmd constantAssigns in
    make_labeled_transaction stmt_id tmps_requested (constantAssigns @ ccmds)
      
      
  method private translate_basic_block_cmd (instr:instr) context:c_cmd_t =
    let ops = ops_provider#get_c_cmd_operations context in
    match instr with
    | Set (lhs,rhs,loc) -> 
      begin
	env#set_current_location loc ;
	make_c_cmd_block (ops @ (assignment_translator#translate context loc lhs rhs ))
      end
    | Call (ret, f, args, loc) ->
      begin
	env#set_current_location loc ;
	make_c_cmd_block (ops @ (call_translator#translate context loc ret f args ))
      end
    | Asm (_,templates,asmoutputs,asminputs,_,loc) ->
       let asmcode = String.concat ";" (List.map cd#get_string templates) in
       let op = make_c_cmd (OPERATION { op_name = new symbol_t ("asm: " ^ asmcode) ;
                                        op_args = [] }) in
       let asmoutputs =
         List.concat
           (List.map (fun (_,konstraint,lhs) ->
                let rhs = CnApp ("asm:" ^ asmcode,[],type_of_lval env#get_fdecls lhs) in
                assignment_translator#translate context loc lhs rhs) asmoutputs) in
       let asminputs =
         List.concat
           (List.map (fun (_,konstraint,rhs) ->
                let lhs = (Mem (CnApp ("asm-lhs" ^ asmcode,[],TPtr (type_of_exp env#get_fdecls rhs,[]))),
                           NoOffset) in
                assignment_translator#translate context loc lhs rhs) asminputs)  in
       begin
         env#set_current_location loc ;
         make_c_cmd_block (ops @ [ op ] @ asmoutputs @ asminputs)
       end
      
end

let get_cfg_translator = new cfg_translator_t


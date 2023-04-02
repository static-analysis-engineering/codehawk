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
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open XprUtil
open Xsimplify

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHDictionary
open CCHFileEnvironment
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesCompare
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHCheckValid
open CCHGlobalAssignment
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes
open CCHCommand
open CCHEnvironment
open CCHExpr
open CCHMemoryRegion
open CCHVariable

module B = Big_int_Z

let x2p = xpr_formatter#pr_expr
let pr2s = CHPrettyUtil.pretty_to_string
let fenv = CCHFileEnvironment.file_environment

class num_exp_translator_t 
        (env:c_environment_int)
        (orakel:orakel_int):exp_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls
    
  method translate_exp (ctxt:program_context_int) (e:exp):xpr_t =
    begin
      context <- ctxt ;
      simplify_xpr (self#translate_expr e)
    end
      
  method translate_lhs (ctxt:program_context_int) (lval:lval):variable_t =
    begin context <- ctxt ; self#translate_lval lval end
      
  method private translate_const_expr (c:constant) (t:typ):xpr_t =
    let logmsg () = () in
    match c with
    | CInt (i64,_,_) -> 
      num_constant_expr (mkNumerical_big (B.big_int_of_int64 i64))
    | CChr c -> num_constant_expr (mkNumerical_big (char_const_to_big c))
    | CStr s -> XVar (env#mk_string_address s NoOffset t)
    | _ -> begin logmsg () ;  random_constant_expr end

  method private translate_variable_expr (lval:lval) (typ:typ):xpr_t =
    let lvar = self#translate_lval lval in
    if env#has_constant_offset lvar then
      match orakel#get_external_value context (XVar lvar) with
      | Some vx -> vx
      | _ -> XVar lvar 
    else 
      XVar lvar
    
  method private translate_expr (x:exp):xpr_t =
    let logmsg () = () in
    try
      let ftype = type_of_exp fdecls x in
      match x with
      | Const c -> self#translate_const_expr c ftype
      | CastE (TPtr _,e) when exp_is_zero e -> zero_constant_expr
      | CastE (TInt _, CastE (TPtr _,e)) when exp_is_zero e -> zero_constant_expr
      | Lval lval -> self#translate_variable_expr lval ftype 
      | SizeOf t -> size_of_type fdecls t
      | SizeOfE e -> size_of_exp_type fdecls e
      | SizeOfStr s ->
         let (_,_,len) = mk_constantstring s in int_constant_expr len
      | BinOp (op,x1,x2,ty) -> self#translate_binop_expr op x1 x2 ty
      | UnOp (op,x1,_) -> self#translate_unop_expr op x1
      | CastE (_, e) -> self#translate_expr e
      | AddrOf lval
	| StartOf lval -> self#translate_address lval ftype
      | CnApp ("ntp", [ Some (Const (CStr s))],_)
        | CnApp ("ntp", [ Some (CastE (_,Const (CStr s))) ],_) ->
         XConst (IntConst (mkNumerical (String.length s)))
      | _ -> begin logmsg() ; random_constant_expr end
    with
    | CCHFailure p | CHFailure p ->
       raise (CCHFailure
                (LBLOCK [ STR "Error in translating exp " ; exp_to_pretty x ; 
			  STR ": "  ; p ]))

  method private externalize_offset offset =
    let default = CnApp ("variable-index",[],TInt (IInt,[])) in
    let externalize_exp e =
      match self#translate_expr e with
      | XConst (IntConst n) -> make_constant_exp n
      | _ -> default in
    match offset with
    | NoOffset -> NoOffset
    | Field (f,o) -> Field (f,self#externalize_offset o)
    | Index (e,o) -> Index (externalize_exp e, self#externalize_offset o)

  method private translate_lval lval =
    match lval with
    | (Var (_,vid),offset) when vid > 0 ->
       let vinfo = env#get_varinfo vid in
       let eoffset = self#externalize_offset offset in
       let otype = type_of_offset env#get_fdecls vinfo.vtype offset in
       if vinfo.vaddrof && vinfo.vglob then
         env#mk_global_memory_variable vinfo eoffset otype NUM_VAR_TYPE
       else if vinfo.vaddrof then
         env#mk_stack_memory_variable vinfo eoffset otype NUM_VAR_TYPE
       else
         env#mk_program_var vinfo eoffset NUM_VAR_TYPE
    | (Var _,_) -> env#mk_temp NUM_VAR_TYPE
    | (Mem e,offset) ->
       match self#translate_exp context e with
       | XVar v when env#is_memory_address v ->
          let (memref,moffset) = env#get_memory_address v in
          env#mk_memory_variable memref#index (add_offset moffset offset) NUM_VAR_TYPE
       | XVar v when env#is_initial_value v ->
          let memref = env#get_variable_manager#memrefmgr#mk_external_reference
                         v (type_of_lval fdecls lval) in
          env#mk_memory_variable memref#index offset NUM_VAR_TYPE
       | XVar v -> env#mk_temp NUM_VAR_TYPE
       | x -> env#mk_temp NUM_VAR_TYPE
       
  method private translate_unop_expr op x = 
    match op with
    | Neg  -> XOp (XNeg,  [ self#translate_expr x ])
    | BNot -> XOp (XBNot, [ self#translate_expr x ])
    | LNot -> XOp (XLNot, [ self#translate_expr x ])
      
  method private translate_address lval ftype:xpr_t =
    let vmgr = env#get_variable_manager in
    let logmsg () = () in
    match lval with
    | (Var (_,vid),offset) when vid > 0 ->
       let vinfo = env#get_varinfo vid in
       if vinfo.vglob then
         XVar (env#mk_global_address_value vinfo offset ftype)
       else
         XVar (env#mk_stack_address_value vinfo offset ftype)
    | (Var _,_) -> random_constant_expr
    | (Mem e,offset) ->
       let memxpr = self#translate_expr e in
       begin
         match memxpr with
         | XVar v when env#is_initial_value v || env#is_function_return_value v ->
            let memref = vmgr#memrefmgr#mk_external_reference v ftype in
            XVar (env#mk_memory_address_value memref#index offset)
         | XVar v when env#is_memory_address v ->
            let (memref,moffset) = env#get_memory_address v in
            XVar (env#mk_memory_address_value memref#index (add_offset moffset offset))
         | _ ->
            begin logmsg () ; random_constant_expr end
       end
      
  method private translate_binop_expr op x1 x2 ty =
    let ty = fenv#get_type_unrolled ty in
    let result = match op with
      | PlusA  -> XOp (XPlus,  [ self#translate_expr x1 ; self#translate_expr x2 ])
      | MinusA -> XOp (XMinus, [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Mult   -> XOp (XMult,  [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Div    -> XOp (XDiv,   [ self#translate_expr x1 ; self#translate_expr x2 ])
      | PlusPI 
      | IndexPI ->
	let targetTyp = match ty with
	  | (TPtr (tty,_)) -> tty
	  | _ ->
             raise (CCHFailure 
		      (LBLOCK [ STR "Application of PlusPI to non-pointer type: " ; 
				typ_to_pretty ty ])) in
	let elementSize = size_of_type fdecls targetTyp in
	XOp (XPlus, [ self#translate_expr x1 ; 
		      XOp (XMult, [ elementSize ; self#translate_expr x2 ])])
      | MinusPP ->
	begin
	  match fenv#get_type_unrolled (type_of_exp fdecls x1) with
	  | TPtr (elTy,_) ->
	    let elementSize = size_of_type fdecls elTy in
	    XOp (XDiv, [ XOp (XMinus, [ self#translate_expr x1 ; self#translate_expr x2 ]) ; 
			 elementSize ])
	  | t ->
             raise (CCHFailure 
		      (LBLOCK [ STR "Application of MinusPP to non-pointer type: " ; 
				typ_to_pretty t]))
	end
      | MinusPI ->
	let elementSize = size_of_type fdecls ty in
	XOp (XMinus, [ self#translate_expr x1 ; 
		       XOp (XMult, [ elementSize ; self#translate_expr x2 ])])
      | Mod     -> XOp (XMod,     [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Shiftlt -> XOp (XShiftlt, [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Shiftrt -> XOp (XShiftrt, [ self#translate_expr x1 ; self#translate_expr x2 ])
      | BAnd    -> XOp (XBAnd,    [ self#translate_expr x1 ; self#translate_expr x2 ])
      | BOr     -> XOp (XBOr,     [ self#translate_expr x1 ; self#translate_expr x2 ])
      | BXor    -> XOp (XBXor,    [ self#translate_expr x1 ; self#translate_expr x2 ])
      | LAnd    -> XOp (XLAnd,    [ self#translate_expr x1 ; self#translate_expr x2 ])
      | LOr     -> XOp (XLOr,     [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Lt      -> XOp (XLt,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Gt      -> XOp (XGt,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Le      -> XOp (XLe,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Ge      -> XOp (XGe,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Ne      -> XOp (XNe,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Eq      -> XOp (XEq,      [ self#translate_expr x1 ; self#translate_expr x2 ]) in
    simplify_xpr result

  method translate_condition context c =
    let tmpProvider = (fun () -> env#mk_num_temp) in
    let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
    let make_assume (x:xpr_t) =
      let trivial b = match b with TRUE | RANDOM -> true | _ -> false in
      let (code,bExp) = 
	let skip = make_c_nop () in
	if Xprt.is_zero x then (skip,FALSE) 
	else if Xprt.is_one x then (skip,TRUE)
	else match x with
	| XOp (XLNot, [ y ]) when Xprt.is_one y -> (skip,FALSE)
	| _ -> xpr2boolexpr tmpProvider cstProvider x in
      let assume = if trivial bExp then make_c_nop () else make_c_cmd (make_assert bExp) in
      make_c_cmd_block [ code ; assume ] in
    let notc = match c with
      | BinOp (Eq, e1, e2, t) -> BinOp (Ne,e1,e2,t)
      | BinOp (Ne, e1, e2, t) -> BinOp (Eq,e1,e2,t)
      | BinOp (Ge, e1, e2, t) -> BinOp (Lt,e1,e2,t)
      | BinOp (Gt, e1, e2, t) -> BinOp (Le,e1,e2,t)
      | BinOp (Le, e1, e2, t) -> BinOp (Gt,e1,e2,t)
      | BinOp (Lt, e1, e2, t) -> BinOp (Ge,e1,e2,t)
      | UnOp (LNot, e,_) -> e
      | _ -> UnOp (LNot, c, type_of_exp fdecls c) in
    let _ = env#start_transaction in
    let then_expr = self#translate_exp context c in
    let then_assert = [ make_assume then_expr ] in
    let (tmps,constantAssigns) = env#end_transaction in
    let constantAssigns = List.map make_c_cmd constantAssigns in
    let then_cond =
      make_labeled_transaction
        env#get_current_stmt_id tmps (constantAssigns @ then_assert) in
    let _ = env#start_transaction in
    let else_expr = self#translate_exp context notc in
    let else_assert = [ make_assume else_expr ] in
    let (tmps,constantAssigns) = env#end_transaction in
    let constantAssigns = List.map make_c_cmd constantAssigns in
    let else_cond =
      make_labeled_transaction
        env#get_current_stmt_id tmps (constantAssigns @ else_assert ) in
    (then_cond,else_cond)
    
end

class sym_pointersets_exp_translator_t
        (env:c_environment_int)
        (orakel:orakel_int):exp_translator_int =
object (self)
     
  val mutable context = mk_program_context ()
  val memregmgr = env#get_variable_manager#memregmgr
  val fdecls = env#get_fdecls

  (* --------------------------- lhs translation ---------------------------- *)

  method translate_lhs (ctxt:program_context_int) (lval:lval):variable_t =
    begin context <- ctxt ; self#translate_lhs_lval lval end

  method private externalize_offset offset =
    let default = CnApp ("variable-index",[],TInt (IInt,[])) in
    let externalize_exp e =
      match self#translate_lhs_expr e with
      | XConst (IntConst n) -> make_constant_exp n
      | _ -> default in
    match offset with
    | NoOffset -> NoOffset
    | Field (f,o) -> Field (f,self#externalize_offset o)
    | Index (e,o) -> Index (externalize_exp e, self#externalize_offset o)
                   
  method private translate_lhs_lval (lval:lval) =
    match lval with
    | (Var (_,vid),offset) when vid > 0 ->
       let vinfo = env#get_varinfo vid in
       let eoffset = self#externalize_offset offset in
       let otype = type_of_offset env#get_fdecls vinfo.vtype offset in
       if vinfo.vaddrof && vinfo.vglob then
         env#mk_global_memory_variable vinfo eoffset otype SYM_VAR_TYPE
       else if vinfo.vaddrof then
         env#mk_stack_memory_variable vinfo eoffset otype SYM_VAR_TYPE
       else
         env#mk_program_var vinfo eoffset SYM_VAR_TYPE
    | (Var _,_) -> env#mk_temp SYM_VAR_TYPE
    | (Mem e,offset) ->
       match self#translate_lhs_expr e with
       | XVar v when env#is_memory_address v ->
          let (memref,moffset) = env#get_memory_address v in
          env#mk_memory_variable memref#index (add_offset moffset offset) SYM_VAR_TYPE
       | _ ->
          env#mk_temp SYM_VAR_TYPE

  method private translate_lhs_const_expr (c:constant) (t:typ):xpr_t =
    let logmsg () = () in
    match c with
    | CInt (i64,_,_) -> 
      num_constant_expr (mkNumerical_big (B.big_int_of_int64 i64))
    | CChr c -> num_constant_expr (mkNumerical_big (char_const_to_big c))
    | CStr s -> XVar (env#mk_string_address s NoOffset t)
    | _ -> begin logmsg () ;  random_constant_expr end

  method private translate_lhs_variable_expr (lval:lval) (typ:typ):xpr_t =
    let lvar = self#translate_lhs_lval lval in
    if env#has_constant_offset lvar then
      match orakel#get_external_value context (XVar lvar) with
      | Some vx -> vx
      | _ -> XVar lvar
    else
      XVar lvar

  method private translate_lhs_expr (x:exp):xpr_t =
    let logmsg () = () in
    try
      let ftype = type_of_exp fdecls x in
      match x with
      | Const c -> self#translate_lhs_const_expr c ftype
      | CastE (TPtr _,e) when exp_is_zero e -> zero_constant_expr
      | CastE (TInt _, CastE (TPtr _,e)) when exp_is_zero e -> zero_constant_expr
      | Lval lval -> self#translate_lhs_variable_expr lval ftype 
      | SizeOf t -> size_of_type fdecls t
      | SizeOfE e -> size_of_exp_type fdecls e
      | SizeOfStr s ->
         let (_,_,len) = mk_constantstring s in int_constant_expr len
      | BinOp (op,x1,x2,ty) -> self#translate_lhs_binop_expr op x1 x2 ty
      | UnOp (op,x1,_) -> self#translate_lhs_unop_expr op x1
      | CastE (_, e) -> self#translate_lhs_expr e
      | AddrOf lval
	| StartOf lval -> self#translate_lhs_address lval ftype
      | CnApp ("ntp", [ Some (Const (CStr s))],_)
        | CnApp ("ntp", [ Some (CastE (_,Const (CStr s))) ],_) ->
         XConst (IntConst (mkNumerical (String.length s)))
      | _ -> begin logmsg() ; random_constant_expr end
    with
    | CCHFailure p | CHFailure p ->
       raise (CCHFailure (LBLOCK [ STR "Error in translating exp " ; exp_to_pretty x ; 
				   STR ": "  ; p ]))

  method private translate_lhs_unop_expr op x = 
    match op with
    | Neg  -> XOp (XNeg,  [ self#translate_lhs_expr x ])
    | BNot -> XOp (XBNot, [ self#translate_lhs_expr x ])
    | LNot -> XOp (XLNot, [ self#translate_lhs_expr x ])
      
  method private translate_lhs_address lval ftype:xpr_t =
    let vmgr = env#get_variable_manager in
    let logmsg () = () in
    match lval with
    | (Var (_,vid),offset) when vid > 0 ->
       let vinfo = env#get_varinfo vid in
       if vinfo.vglob then
         XVar (env#mk_global_address_value vinfo offset ftype)
       else
         XVar (env#mk_stack_address_value vinfo offset ftype)
    | (Var _,_) -> random_constant_expr
    | (Mem e,offset) ->
       let memxpr = self#translate_lhs_expr e in
       begin
         match memxpr with
         | XVar v when env#is_initial_value v || env#is_function_return_value v ->
            let memref = vmgr#memrefmgr#mk_external_reference v ftype in
            XVar (env#mk_memory_address_value memref#index offset)
         | XVar v when env#is_memory_address v -> XVar v
         | _ ->
            begin logmsg () ; random_constant_expr end
       end
      
  method private translate_lhs_binop_expr op x1 x2 ty =
    let ty = fenv#get_type_unrolled ty in
    let result = match op with
      | PlusA  -> XOp (XPlus,  [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | MinusA -> XOp (XMinus, [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Mult   -> XOp (XMult,  [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Div    -> XOp (XDiv,   [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | PlusPI 
      | IndexPI ->
	let targetTyp = match ty with
	  | (TPtr (tty,_)) -> tty
	  | _ -> raise (CCHFailure 
			  (LBLOCK [ STR "Application of PlusPI to non-pointer type: " ; 
				    typ_to_pretty ty ])) in
	let elementSize = size_of_type fdecls targetTyp in
	XOp (XPlus, [ self#translate_lhs_expr x1 ; 
		      XOp (XMult, [ elementSize ; self#translate_lhs_expr x2 ])])
      | MinusPP ->
	begin
	  match fenv#get_type_unrolled (type_of_exp fdecls x1) with
	  | TPtr (elTy,_) ->
	    let elementSize = size_of_type fdecls elTy in
	    XOp (XDiv, [ XOp (XMinus, [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ]) ; 
			 elementSize ])
	  | t -> raise (CCHFailure 
			  (LBLOCK [ STR "Application of MinusPP to non-pointer type: " ; 
				    typ_to_pretty t]))
	end
      | MinusPI ->
	let elementSize = size_of_type fdecls ty in
	XOp (XMinus, [ self#translate_lhs_expr x1 ; 
		       XOp (XMult, [ elementSize ; self#translate_lhs_expr x2 ])])
      | Mod     -> XOp (XMod,     [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Shiftlt -> XOp (XShiftlt, [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Shiftrt -> XOp (XShiftrt, [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | BAnd    -> XOp (XBAnd,    [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | BOr     -> XOp (XBOr,     [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | BXor    -> XOp (XBXor,    [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | LAnd    -> XOp (XLAnd,    [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | LOr     -> XOp (XLOr,     [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Lt      -> XOp (XLt,      [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Gt      -> XOp (XGt,      [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Le      -> XOp (XLe,      [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Ge      -> XOp (XGe,      [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Ne      -> XOp (XNe,      [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ])
      | Eq      -> XOp (XEq,      [ self#translate_lhs_expr x1 ; self#translate_lhs_expr x2 ]) in
    simplify_xpr result

  (* --------------------------- rhs translation ---------------------------- *)

  method translate_exp (ctxt:program_context_int) (e:exp) =
    begin context <- ctxt ; self#translate_rhs_expr e end
        
  method private translate_rhs_const_expr (c:constant) =
    match c with
    | CStr s -> sym_constant_expr (memregmgr#mk_string_region_sym s)
    | _ -> random_constant_expr             (* TBD, see ref *)

  method private translate_rhs_expr (x:exp):xpr_t = 
    let null_sym = memregmgr#mk_null_sym (-1) in
    let null_constant_expr = XConst (SymSet [ null_sym ]) in
    let default () =
      let s = memregmgr#mk_uninterpreted_sym (pr2s (exp_to_pretty x)) in
      sym_constant_expr s in
    let xpr =
      try
        let typ = fenv#get_type_unrolled (type_of_exp fdecls x) in
        if is_pointer_type typ then
          match x with
          | Const c -> self#translate_rhs_const_expr c
          | CastE (TPtr _,e) when exp_is_zero e -> null_constant_expr
          | CastE (TInt _,CastE (TPtr _,e)) when exp_is_zero e -> null_constant_expr
          | Lval lval -> self#translate_rhs_variable_expr lval
          | AddrOf (Var (vname,vid),_)
            | StartOf (Var (vname,vid),_) when vid > 0 ->
             let vinfo = env#get_varinfo vid in
             let progvar = env#mk_program_var vinfo NoOffset SYM_VAR_TYPE in
             let progvar =
               if env#is_memory_variable progvar then
                 let (memref,_) = env#get_memory_variable progvar in
                 match memref#get_base with
                 | CStackAddress v -> v
                 | CGlobalAddress v -> v
                 | CBaseVar v -> v
                 | _ ->
                    raise (CCHFailure
                             (LBLOCK [ STR "Unexpected memory base for variable: " ;
                                       STR vname ]))
               else
                 progvar in
             if vinfo.vglob then
               let s = memregmgr#mk_global_region_sym progvar in
               sym_constant_expr s
             else
               let s = memregmgr#mk_stack_region_sym progvar in
               sym_constant_expr s
          | BinOp (op,x1,x2,ty) -> self#translate_rhs_binop_expr op x1 x2 ty
          | CastE (_,e) -> self#translate_rhs_expr e
          | _ -> default ()
        else
          random_constant_expr
      with
      | CCHFailure p ->
         raise (CCHFailure (LBLOCK [ STR "Error in translating exp " ; exp_to_pretty x ;
                                     STR ": " ; p ])) in
    if is_pointer_type (fenv#get_type_unrolled (type_of_exp fdecls x))
       && is_random xpr then default () else xpr
    
  method private translate_rhs_variable_expr (lval:lval) =
    let lvar = self#translate_lhs_lval lval in
    match orakel#get_external_value context (XVar lvar) with
    | Some vx ->
       begin
         match vx with
         | XVar v when env#is_memory_address v ->
            let memref = env#get_memory_reference v in
            let base = memref#get_base in
            let regionsym = memregmgr#mk_base_region_sym base in
            sym_constant_expr regionsym
         | _ -> XVar lvar
       end            
    | _ -> XVar lvar
         
  method private translate_rhs_binop_expr op x1 x2 ty =
    match op with
    | PlusPI | IndexPI | MinusPI -> self#translate_rhs_expr x1
    | _ -> random_constant_expr    (* TBD, see ref *)

  method private get_standard_condition cond =
    None       (* TBD, see ref *)

  method translate_condition cfgcontext cond =
    let nullsyms = memregmgr#get_null_syms in
    let rec is_zero e = match e with
      | Const (CInt (i64,_,_)) -> (Int64.compare i64 Int64.zero) = 0
      | CastE (_, e) -> is_zero e
      | _ -> false in           
    match cond with
    | BinOp (Ne, CastE(_,(Lval lval)), e, _) when is_zero e ->
       let symvar = self#translate_lhs_lval lval in
       if symvar#isTmp then
         (SKIP,SKIP)
       else
         let tcond = ASSERT (DISJOINT (symvar, nullsyms)) in
         let fcond = ASSERT (SUBSET (symvar, nullsyms)) in
         (tcond,fcond)
    | BinOp (Eq, CastE(_,(Lval lval)), e, _) when is_zero e ->
       let symvar = self#translate_lhs_lval lval in
       if symvar#isTmp then
         (SKIP,SKIP)
       else
         let tcond = ASSERT (SUBSET (symvar, nullsyms)) in
         let fcond = ASSERT (DISJOINT (symvar, nullsyms)) in
         (tcond,fcond)
    |_ ->
      (SKIP,SKIP)

end

(* only used to translate the lhs of an assignment *)
class sym_exp_translator_t (env:c_environment_int) orakel:exp_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls

  method translate_exp (ctxt:program_context_int) (e:exp) =
    begin context <- ctxt ; self#translate_expr e end

  method translate_lhs (ctxt:program_context_int) (lval:lval) =
    begin context <- ctxt ; self#translate_lval lval end

  method private translate_const_expr (c:constant):xpr_t =
    let logmsg () = () in
    match c with
    | CInt (i64,_,_) -> 
      num_constant_expr (mkNumerical_big (B.big_int_of_int64 i64))
    | CChr c -> num_constant_expr (mkNumerical_big (char_const_to_big c))
    | _ -> begin logmsg () ;  random_constant_expr end

  method private translate_expr (x:exp):xpr_t =
    let ftype = type_of_exp fdecls x in
    match x with
    | Const c -> self#translate_const_expr c
    | CastE (_,xx) -> self#translate_expr xx
    | Lval lval -> self#translate_variable_expr lval ftype
    | AddrOf lval
      | StartOf lval -> self#translate_address lval ftype
    | BinOp (op,x1,x2,ty) -> self#translate_binop_expr op x1 x2 ty
    | _ -> random_constant_expr

  method private translate_address lval ftype:xpr_t =
    let vmgr = env#get_variable_manager in
    let logmsg () = () in
    match lval with
    | (Var (_,vid),offset) ->
       let vinfo = env#get_varinfo vid in
       if vinfo.vglob then
         XVar (env#mk_global_address_value vinfo offset ftype)
       else
         XVar (env#mk_stack_address_value vinfo offset ftype)
    | (Mem e,offset) ->
       let memxpr = self#translate_expr e in
       begin
         match memxpr with
         | XVar v when env#is_initial_value v || env#is_function_return_value v ->
            let memref = vmgr#memrefmgr#mk_external_reference v ftype in
            XVar (env#mk_memory_address_value memref#index offset)
         | XVar v when env#is_memory_address v -> XVar v
         | _ ->
            begin logmsg () ; random_constant_expr end
       end

  method private translate_binop_expr op x1 x2 ty =
    let result = match op with
      | Lt      -> XOp (XLt,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Gt      -> XOp (XGt,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Le      -> XOp (XLe,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Ge      -> XOp (XGe,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Ne      -> XOp (XNe,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | Eq      -> XOp (XEq,      [ self#translate_expr x1 ; self#translate_expr x2 ])
      | _ -> random_constant_expr in
    simplify_xpr result

  method private translate_variable_expr (lval:lval) (typ:typ):xpr_t =
    let lvar = self#translate_lval lval in
    if env#has_constant_offset lvar then
      match orakel#get_external_value context (XVar lvar) with
      | Some vx -> vx
      | _ -> XVar lvar
    else
      XVar lvar
    
  method private externalize_offset offset =
    let default = CnApp ("variable-index",[],TInt (IInt,[])) in
    let externalize_exp e =
      match self#translate_expr e with
      | XConst (IntConst n) -> make_constant_exp n
      | _ -> default in
    match offset with
    | NoOffset -> NoOffset
    | Field (f,o) -> Field (f,self#externalize_offset o)
    | Index (e,o) -> Index (externalize_exp e, self#externalize_offset o)

  method private translate_lval lval =
    let rec is_constant_index offset result =
      result &&
        match offset with
        | NoOffset -> true
        | Field (f,o) -> is_constant_index o result
        | Index (e,o) ->
           match e with CnApp _ -> false | _ -> is_constant_index o result in
    match lval with
    | (Var (_,vid),offset) ->
       let vinfo = env#get_varinfo vid in
       let eoffset = self#externalize_offset offset in
       if is_constant_index eoffset true then
         let otype = type_of_offset env#get_fdecls vinfo.vtype offset in
         if vinfo.vaddrof && vinfo.vglob then
           env#mk_global_memory_variable vinfo eoffset otype SYM_VAR_TYPE
         else if vinfo.vaddrof then
           env#mk_stack_memory_variable vinfo eoffset otype SYM_VAR_TYPE
         else
           env#mk_program_var vinfo eoffset SYM_VAR_TYPE
       else
         env#mk_temp SYM_VAR_TYPE
    | (Mem e,offset) ->
       match self#translate_exp context e with
       | XVar v when env#is_memory_address v ->
          let (memref,moffset) = env#get_memory_address v in
          env#mk_memory_variable memref#index (add_offset moffset offset) SYM_VAR_TYPE
       | XVar v when env#is_initial_value v ->
          let memref = env#get_variable_manager#memrefmgr#mk_external_reference
                         v (type_of_lval fdecls lval) in
          env#mk_memory_variable memref#index offset SYM_VAR_TYPE
       | _ ->
          env#mk_temp SYM_VAR_TYPE


  method translate_condition context c =
    let make_assume (x:xpr_t) =
      if is_zero x || is_false x then (ASSERT FALSE,ASSERT TRUE)
      else if is_one x || is_true x then (ASSERT TRUE,ASSERT FALSE)
      else (SKIP,SKIP) in
    let x = self#translate_exp context c in
    make_assume x
                                                                    

end

    
let get_num_exp_translator env orakel =
  new num_exp_translator_t env orakel

let get_sym_exp_translator env orakel =
  new sym_exp_translator_t env orakel

let get_sym_pointersets_exp_translator env orakel =
  new sym_pointersets_exp_translator_t env orakel
    

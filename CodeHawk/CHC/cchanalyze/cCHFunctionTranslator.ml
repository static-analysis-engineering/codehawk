(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* xprlib *)
open Xprt
open XprTypes
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHFileContract
open CCHFileEnvironment
open CCHLibTypes
open CCHTypesTransformer
open CCHTypesUtil

(* cchanalyze *)
open CCHAnalysisTypes
open CCHAssignmentTranslator
open CCHCallTranslator
open CCHCfgTranslator
open CCHCommand
open CCHControlFlowGraph
open CCHExpTranslator

module EU = CCHEngineUtil
module H = Hashtbl

let fenv = CCHFileEnvironment.file_environment


class ptrvar_abstraction_transformer_t
        (replacement:variable_t -> variable_t list) =
object

  inherit code_transformer_t as super

  method! transformCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | ABSTRACT_VARS [v1 ; v2] when v1#isTmp ->
      let vars = replacement v2 in
	ABSTRACT_VARS vars
    | _ -> super#transformCmd cmd

end


let get_replacer_function _env _fname = (fun (_v:variable_t) -> [])


class num_function_translator_t
  (env:c_environment_int)
  (cfg_translator:cfg_translator_int)
  (_exp_translator:exp_translator_int)
  (_call_translator:call_translator_int):function_translator_int =
object (self)

  method private get_deref_assigns formals =
    List.fold_left (fun acc vinfo ->
        let ttyp = fenv#get_type_unrolled vinfo.vtype in
        match ttyp with
        | TPtr ((TInt _ | TFloat _), _) ->
           let (v,vInit,vm,vmInit) =
             env#mk_par_deref_init vinfo NoOffset ttyp NUM_VAR_TYPE in
           (ASSIGN_NUM (v, NUM_VAR vInit))
           :: (ASSIGN_NUM (vm, NUM_VAR vmInit))
           :: acc
        | TPtr (TComp (ckey, _), _) ->
           (List.map
              (fun (v, vInit) -> ASSIGN_NUM (v, NUM_VAR vInit))
              (env#mk_struct_par_deref vinfo ttyp ckey NUM_VAR_TYPE)) @ acc
        | TPtr (TPtr _,_) ->
           let (v, vInit, vm, vmInit) =
             env#mk_par_deref_init vinfo NoOffset ttyp NUM_VAR_TYPE in
           (ASSIGN_NUM (v, NUM_VAR vInit))
           :: (ASSIGN_NUM (vm, NUM_VAR vmInit))
           :: acc
        | _ -> acc) [] formals

  method private assert_global_values globals =
    let contractgvars = file_contract#get_global_variables in
    let table = H.create 3 in
    let tmpProvider = (fun () -> env#mk_num_temp) in
    let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
    let _ = List.iter (fun gv -> H.add table gv.cgv_name gv) contractgvars in
    let _ = env#start_transaction in
    let ccmds =
      List.fold_left (fun acc (vname, _, _, vInit) ->
          if H.mem table vname then
            let gcvar = H.find table vname in
            match gcvar.cgv_value with
            | Some i ->
               let x = XOp (XEq, [XVar vInit ; int_constant_expr i]) in
               let (code,bExp) = xpr2boolexpr tmpProvider cstProvider x in
               (make_c_cmd_block [code ; make_c_cmd (make_assert bExp)]) :: acc
            | _ -> acc
          else acc) [] globals  in
    let (tmps_requested,constantAssigns) = env#end_transaction in
    let constantAssigns = List.map make_c_cmd constantAssigns in
    [make_labeled_transaction 0 tmps_requested (constantAssigns @ ccmds)]

  method translate (f:fundec) =
    let context = mk_program_context () in
    let _ = env#register_program_locals f.sdecls#get_locals NUM_VAR_TYPE in
    let _ = env#register_function_return f.svar.vtype NUM_VAR_TYPE in
    let formals = env#register_formals f.sdecls#get_formals NUM_VAR_TYPE in
    let globalvars =
      List.map f.sdecls#get_varinfo_by_vid (get_block_variables f.sbody) in
    let globalvars = List.filter (fun vinfo -> vinfo.vglob) globalvars in
    let contractglobals = file_contract#get_global_variables in
    let contractglobals =
      List.map (fun v ->
          file_environment#get_globalvar_by_name v.cgv_name) contractglobals in
    let globalvars =
      List.fold_left (fun acc v ->
          if List.exists (fun vv ->
                 v.vid = vv.vid) acc then acc else v :: acc)
                     globalvars contractglobals in
    let globals = env#register_globals globalvars NUM_VAR_TYPE in
    let fpreamble =
      List.map (fun (_, _, v, vInit) ->
          ASSIGN_NUM (v, NUM_VAR vInit)) (formals @ globals) in
    let fglobalvalues = self#assert_global_values globals in
    let derefAssigns = self#get_deref_assigns f.sdecls#get_formals in
    let gotos = make_gotos f.sbody in
    let fblock = if gotos#is_goto_function then
	cfg_translator#translate_cfg_breakout_block f.sbody gotos context
      else
	cfg_translator#translate_breakout_block f.sbody gotos context in
    let replacer = get_replacer_function env f.svar.vname in
    let transformer = new ptrvar_abstraction_transformer_t replacer in
    let _ = transformer#transformCode (EU.mkCode fblock) in
    let fbody = EU.mkCode (fglobalvalues @ fpreamble @ derefAssigns @ fblock) in
    let scope = env#get_scope in
    let fsymbol = EU.symbol f.svar.vname in
    let proc =
      EU.mkProcedure fsymbol ~signature:[] ~bindings:[] ~scope ~body:fbody in
    let csystem = EU.mkSystem (new symbol_t "c-system") in
    let _ = csystem#addProcedure proc in
    (None, csystem)

end


let _make_non_negative_assert env (v:variable_t) =
  let tmpProvider = (fun () -> env#mk_num_temp) in
  let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
  let x = XOp (XGe, [XVar v ; zero_constant_expr]) in
  let (code,bExp) = xpr2boolexpr tmpProvider cstProvider x in
  make_c_cmd_block [code; make_c_cmd (make_assert bExp)]


let _make_positive_assert env (v:variable_t) =
  let tmpProvider = (fun () -> env#mk_num_temp) in
  let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
  let x = XOp (XGt, [XVar v ; zero_constant_expr]) in
  let (code,bExp) = xpr2boolexpr tmpProvider cstProvider x in
  make_c_cmd_block [code ; make_c_cmd (make_assert bExp)]


let make_range_assert env (v:variable_t) (lb:numerical_t) (ub:numerical_t) =
  let tmpProvider = (fun () -> env#mk_num_temp) in
  let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
  let lbx = XOp (XGe, [XVar v ; num_constant_expr lb]) in
  let ubx = XOp (XLe, [XVar v ; num_constant_expr ub])  in
  let (lbcode,bLbExp) = xpr2boolexpr tmpProvider cstProvider lbx in
  let (ubcode,bUbExp) = xpr2boolexpr tmpProvider cstProvider ubx in
  make_c_cmd_block [
      lbcode;
      ubcode;
      make_c_cmd (make_assert bLbExp);
      make_c_cmd (make_assert bUbExp)]


class interval_function_translator_t
  (env:c_environment_int)
  (cfg_translator:cfg_translator_int)
  (_exp_translator:exp_translator_int)
  (_call_translator:call_translator_int):function_translator_int =
object

  method translate (f:fundec) =
    let context = mk_program_context () in
    let _ = env#register_program_locals f.sdecls#get_locals NUM_VAR_TYPE in
    let _ = env#register_function_return f.svar.vtype NUM_VAR_TYPE in
    let formals = env#register_formals f.sdecls#get_formals NUM_VAR_TYPE in
    let globalvars =
      List.map f.sdecls#get_varinfo_by_vid (get_block_variables f.sbody) in
    let globalvars = List.filter (fun vinfo -> vinfo.vglob) globalvars in
    let globals = env#register_globals globalvars NUM_VAR_TYPE in
    let preamble =
      List.map (fun (_,_,v,vInit) ->
          ASSIGN_NUM (v, NUM_VAR vInit)) (formals @ globals) in
    let _ = env#start_transaction in
    let rangeconstraints =
      List.fold_left (fun acc (vname, vtype, _, vInit) ->
          match vtype with
          | (TInt (IChar, _)) | (TInt (ISChar, _)) ->
             let _= chlog#add "range constraint"
                  (LBLOCK [STR vname])  in
             (make_range_assert
                env vInit (mkNumerical (-128)) (mkNumerical 127)) :: acc
          | _ -> acc) [] (formals @ globals)  in
    let (tmps,rangecode) = env#end_transaction  in
    let rangecode = List.map make_c_cmd rangecode in
    let rangeconstraints =
      make_labeled_transaction 0 tmps (rangecode @ rangeconstraints) in
    let gotos = make_gotos f.sbody in
    let fblock = if gotos#is_goto_function then
	cfg_translator#translate_cfg_breakout_block f.sbody gotos context
      else
	cfg_translator#translate_breakout_block f.sbody gotos context in
    let replacer = get_replacer_function env f.svar.vname in
    let transformer = new ptrvar_abstraction_transformer_t replacer in
    let _ = transformer#transformCode (EU.mkCode fblock) in
    let derefAssigns = [] in                                  (* TBD: see ref *)
    let fbody =
      EU.mkCode ([rangeconstraints] @ preamble @ derefAssigns @ fblock) in
    let scope = env#get_scope in
    let fsymbol = EU.symbol f.svar.vname in
    let proc =
      EU.mkProcedure fsymbol ~signature:[] ~bindings:[] ~scope ~body:fbody in
    let csystem = EU.mkSystem (new symbol_t "c-system") in
    let _ = csystem#addProcedure proc in
    (None,csystem)

end


let get_valueset_preamble (env:c_environment_int) fundec =
  let arrayLocals =
    List.filter (fun v -> is_array_type v.vtype) (fundec.sdecls#get_locals) in
  let arrayLocals =
    List.map (fun v -> (v,NoOffset)) arrayLocals in
  let arrayLocals =
    List.map (fun (v,offset) ->
        (true,env#mk_stack_address_value v offset v.vtype)) arrayLocals in
  let pointerFormals =
    List.filter (fun v -> is_pointer_type v.vtype) (fundec.sdecls#get_formals) in
  let pointerFormals =
    List.map (fun v ->
        (false,env#mk_formal_ptr_base_variable v NUM_VAR_TYPE)) pointerFormals in
  let contractglobals =
    List.filter (fun v -> v.cgv_notnull) file_contract#get_global_variables in
  let contractglobals =
    List.map (fun v ->
        file_environment#get_globalvar_by_name v.cgv_name) contractglobals in
  let contractglobals =
    List.map (fun v ->
        (true,env#mk_program_var v NoOffset NUM_VAR_TYPE)) contractglobals in

  let parDerefs = [] in
  match (arrayLocals @ pointerFormals @ parDerefs @ contractglobals)  with
    [] -> SKIP
  | l ->
    let domainOps = List.map (fun (notnull,v) ->
      let init = if notnull then "initialize" else "initialize_with_null" in
      DOMAIN_OPERATION (
          ["valuesets"],
	  { op_name = new symbol_t init;
	    op_args = [(v#getName#getBaseName, v, READ)]} )) l in
    CODE (new symbol_t "value sets", EU.mkCode domainOps)


class valueset_function_translator_t
  (env:c_environment_int)
  (cfg_translator:cfg_translator_int)
  (_exp_translator:exp_translator_int)
  (_call_translator:call_translator_int):function_translator_int =
object

  method translate (f:fundec) =
    let context = mk_program_context () in
    let _ = env#register_program_locals f.sdecls#get_locals NUM_VAR_TYPE in
    let _ = env#register_function_return f.svar.vtype NUM_VAR_TYPE in
    let formals = env#register_formals f.sdecls#get_formals NUM_VAR_TYPE in
    let preamble =
      List.map (fun (_,_,v,vInit) -> ASSIGN_NUM (v, NUM_VAR vInit)) formals in
    let gotos = make_gotos f.sbody in
    let fblock = if gotos#is_goto_function then
	cfg_translator#translate_cfg_breakout_block f.sbody gotos context
      else
	cfg_translator#translate_breakout_block f.sbody gotos context in
    let valuesetPreamble = get_valueset_preamble env f in
    let derefAssigns = [] in
    let fbody =
      EU.mkCode ([valuesetPreamble] @ preamble @ derefAssigns @ fblock) in
    let scope = env#get_scope in
    let fsymbol = EU.symbol f.svar.vname in
    let proc =
      EU.mkProcedure fsymbol ~signature:[] ~bindings:[] ~scope ~body:fbody in
    let csystem = EU.mkSystem (new symbol_t "c-system") in
    let _ = csystem#addProcedure proc in
    (None,csystem)

end


class symbolicsets_function_translator_t
  (env:c_environment_int)
  (cfg_translator:cfg_translator_int)
  (_exp_translator:exp_translator_int)
  (_call_translator:call_translator_int):function_translator_int =
object

  method translate (f:fundec) =
    let context = mk_program_context () in
    let _ = env#register_program_locals f.sdecls#get_locals SYM_VAR_TYPE in
    let _ = env#register_function_return f.svar.vtype SYM_VAR_TYPE in
    let formals = env#register_formals f.sdecls#get_formals SYM_VAR_TYPE in
    let callvar = env#mk_call_vars in
    let callvarassign = [ASSIGN_SYM (callvar, SYM env#get_p_entry_sym)] in
    let preamble =
      List.map (fun (_, _, v, vInit) -> ASSIGN_SYM (v, SYM_VAR vInit)) formals in
    let gotos = make_gotos f.sbody in
    let fblock = if gotos#is_goto_function then
	cfg_translator#translate_cfg_breakout_block f.sbody gotos context
      else
	cfg_translator#translate_breakout_block f.sbody gotos context in
    let derefAssigns = [] in
    let addressAssigns = [] in
    let fbody =
      EU.mkCode
        (preamble @ callvarassign @ derefAssigns @ addressAssigns @ fblock) in
    let scope = env#get_scope in
    let fsymbol = EU.symbol f.svar.vname in
    let proc =
      EU.mkProcedure fsymbol ~signature:[] ~bindings:[] ~scope ~body:fbody in
    let csystem = EU.mkSystem (new symbol_t "c-system") in
    let _ = csystem#addProcedure proc in
    (None, csystem)

end


class statesets_function_translator_t
        (env:c_environment_int)
        (cfg_translator:cfg_translator_int)
        (_exp_translator:exp_translator_int)
        (_call_translator:call_translator_int):function_translator_int =
object

  method translate (f:fundec) =
    let context = mk_program_context () in
    let _ = env#register_program_locals f.sdecls#get_locals SYM_VAR_TYPE in
    let _ = env#register_function_return f.svar.vtype SYM_VAR_TYPE in
    let formals = env#register_formals f.sdecls#get_formals SYM_VAR_TYPE in
    let preamble =
      List.map (fun (_, _, v, vInit) -> ASSIGN_SYM (v, SYM_VAR vInit)) formals in
    let gotos = make_gotos f.sbody in
    let fblock = if gotos#is_goto_function then
	cfg_translator#translate_cfg_breakout_block f.sbody gotos context
      else
	cfg_translator#translate_breakout_block f.sbody gotos context in
    let derefAssigns = [] in
    let addressAssigns = [] in
    let fbody = EU.mkCode ( preamble @ derefAssigns @ addressAssigns @ fblock) in
    let scope = env#get_scope in
    let fsymbol = EU.symbol f.svar.vname in
    let proc =
      EU.mkProcedure fsymbol ~signature:[] ~bindings:[] ~scope ~body:fbody in
    let csystem = EU.mkSystem (new symbol_t "c-system") in
    let _ = csystem#addProcedure proc in
    (None, csystem)

end


class sym_pointersets_function_translator_t
  (env:c_environment_int)
  (cfg_translator:cfg_translator_int)
  (_exp_translator:exp_translator_int)
  (_call_translator:call_translator_int)
  (_external_addresses:variable_t list):function_translator_int =
object

  method translate (f:fundec) =
    let context = mk_program_context () in
    let memregmgr = env#get_variable_manager#memregmgr in
    let _ = env#register_program_locals f.sdecls#get_locals SYM_VAR_TYPE in
    let _ = env#register_function_return f.svar.vtype SYM_VAR_TYPE in
    let formals = env#register_formals f.sdecls#get_formals SYM_VAR_TYPE in
    let preamble =
      List.fold_left
        (fun acc (_vname, vtype, v, vInit) ->
          if is_pointer_type vtype then
            let regsym = memregmgr#mk_external_region_sym vInit in
            let nullsym = memregmgr#mk_null_sym regsym#getSeqNumber in
            (BRANCH [EU.mkCode [ASSIGN_SYM (v, SYM regsym)];
                     EU.mkCode [ASSIGN_SYM (v, SYM nullsym)]]) :: acc
          else acc) [] formals in
    let gotos = make_gotos f.sbody in
    let fblock =
      if gotos#is_goto_function then
        cfg_translator#translate_cfg_breakout_block f.sbody gotos context
      else
        cfg_translator#translate_breakout_block f.sbody gotos context in
    let fbody = EU.mkCode (preamble @ fblock) in
    let scope = env#get_scope in
    let fsymbol = EU.symbol f.svar.vname in
    let proc =
      EU.mkProcedure fsymbol ~signature:[] ~bindings:[] ~scope ~body:fbody in
    let csystem = EU.mkSystem (new symbol_t "c-system") in
    let _ = csystem#addProcedure proc in
    (None, csystem)

end


let get_num_translator env orakel ops_provider =
  let expTranslator = get_num_exp_translator env orakel in
  let assignmentTranslator = get_num_assignment_translator env expTranslator in
  let callTranslator = get_num_call_translator env orakel expTranslator in
  let cfgTranslator =
    get_cfg_translator
      env assignmentTranslator callTranslator expTranslator ops_provider in
  new num_function_translator_t env cfgTranslator expTranslator callTranslator


let get_interval_translator env orakel ops_provider =
  let expTranslator = get_num_exp_translator env orakel in
  let assignmentTranslator = get_num_assignment_translator env expTranslator in
  let callTranslator = get_num_call_translator env orakel expTranslator in
  let cfgTranslator =
    get_cfg_translator
      env assignmentTranslator callTranslator expTranslator ops_provider in
  new interval_function_translator_t
    env cfgTranslator expTranslator callTranslator


let get_valueset_translator env orakel ops_provider =
  let expTranslator = get_num_exp_translator env orakel in
  let assignmentTranslator = get_num_assignment_translator env expTranslator in
  let callTranslator = get_valueset_call_translator env orakel expTranslator in
  let cfgTranslator =
    get_cfg_translator
      env assignmentTranslator callTranslator expTranslator ops_provider in
  new valueset_function_translator_t
    env cfgTranslator expTranslator callTranslator


let get_symbolicsets_translator (env:c_environment_int) orakel ops_provider =
  let expTranslator = get_sym_exp_translator env orakel in
  let assignmentTranslator = get_sym_assignment_translator env expTranslator in
  let callTranslator = get_sym_call_translator env orakel expTranslator in
  let cfgTranslator =
    get_cfg_translator
      env assignmentTranslator callTranslator expTranslator ops_provider in
  new symbolicsets_function_translator_t
    env cfgTranslator expTranslator callTranslator


let get_statesets_translator (env:c_environment_int) orakel ops_provider =
  let expTranslator = get_sym_exp_translator env orakel in
  let assignmentTranslator =
    get_statesets_assignment_translator env expTranslator in
  let callTranslator = get_stateset_call_translator env orakel expTranslator in
  let cfgTranslator =
    get_cfg_translator
      env assignmentTranslator callTranslator expTranslator ops_provider in
  new statesets_function_translator_t
    env cfgTranslator expTranslator callTranslator


let get_sym_pointersets_translator (env:c_environment_int) orakel ops_provider =
  let expTranslator = get_sym_pointersets_exp_translator env orakel in
  let assignmentTranslator =
    get_sym_pointersets_assignment_translator env expTranslator in
  let callTranslator =
    get_sym_pointersets_call_translator env orakel expTranslator  in
  let cfgTranslator =
    get_cfg_translator
      env assignmentTranslator callTranslator expTranslator ops_provider in
  new sym_pointersets_function_translator_t
    env cfgTranslator expTranslator callTranslator []

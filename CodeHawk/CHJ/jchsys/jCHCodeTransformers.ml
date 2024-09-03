(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHPretty

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHIFSystem

(* jchsys *)
open JCHGlobals

module F = CHOnlineCodeSet.LanguageFactory


(* Adds a method_entry state *)
class method_entry_adder_t (cms:class_method_signature_int) =
  object (self: _)
    inherit code_transformer_t as super

    method private mkCode cmds = chif_system#make_code cms cmds

    method !transformCmd (cmd:(code_int, cfg_int) command_t) =
      match cmd with
    | CFG (s, cfg) ->
	let entry_state = cfg#getEntry in
	let method_entry = F.mkState method_entry_sym (self#mkCode []) in
	let _ = method_entry#addOutgoingEdge entry_state#getLabel in
	let _ = entry_state#addIncomingEdge method_entry_sym in
	let new_cfg = F.mkCFG method_entry cfg#getExit in
	let _ =
	  List.iter
	    (fun s -> new_cfg#addState (cfg#getState s))
	    cfg#getStates in
	CFG (s, new_cfg)
    | _ ->
	super#transformCmd cmd
  end


let add_method_entry (procedure:procedure_int) =
  let cms = retrieve_cms procedure#getName#getSeqNumber in
  let transformer = new method_entry_adder_t cms in
  transformer#transformCode procedure#getBody


(* A code transformer for the case when we want to transform the variables *)
class variable_transformer_t =
  object (self: _)

    inherit code_transformer_t as super

    method transformVar (v:variable_t):variable_t = v

    method transformNumExp (e:numerical_exp_t):numerical_exp_t =
      match e with
      |	NUM _ -> e
      | NUM_VAR v ->
	  NUM_VAR (self#transformVar v)
      | PLUS (x, y) ->
	  PLUS (self#transformVar x,
		self#transformVar y)
      | MINUS (x, y) ->
	  MINUS (self#transformVar x,
		 self#transformVar y)
      | MULT (x, y) ->
	  MULT (self#transformVar x,
		self#transformVar y)
      | DIV (x, y) ->
	  DIV (self#transformVar x,
	       self#transformVar y)

  method transformSymExp (e:symbolic_exp_t):symbolic_exp_t =
    match e with
      | SYM _ -> e
      | SYM_VAR v ->
	  SYM_VAR (self#transformVar v)

  method transformBoolExp (e:boolean_exp_t):boolean_exp_t =
    match e with
      | LEQ (x, y) ->
	  LEQ (self#transformVar x,
	       self#transformVar y)
      | GEQ (x, y) ->
	  GEQ (self#transformVar x,
	       self#transformVar y)
      | LT (x, y) ->
	  LT (self#transformVar x,
	      self#transformVar y)
      | GT (x, y) ->
	  GT (self#transformVar x,
	      self#transformVar y)
      | EQ (x, y) ->
	  EQ (self#transformVar x,
	      self#transformVar y)
      | NEQ (x, y) ->
	  NEQ (self#transformVar x,
	       self#transformVar y)
      | SUBSET (v, l) ->
	  SUBSET (self#transformVar v, l)
      | DISJOINT (v, l) ->
	  DISJOINT (self#transformVar v, l)
      |	_ -> e

  method !transformCmd
           (cmd:(code_int, cfg_int) command_t):(code_int, cfg_int) command_t =
      match cmd with
      | ABSTRACT_VARS l ->
	  ABSTRACT_VARS (List.map self#transformVar l)
      | ABSTRACT_ELTS (a, min, max) ->
	  ABSTRACT_ELTS (self#transformVar a,
			self#transformVar min,
			self#transformVar max)
      | ASSIGN_NUM (x, e) ->
	  ASSIGN_NUM (self#transformVar x,
			self#transformNumExp e)
      | ASSIGN_ARRAY (x, y) ->
	  ASSIGN_ARRAY (self#transformVar x,
			self#transformVar y)
      | INCREMENT (x, n) ->
	  INCREMENT (self#transformVar x, n)
      | ASSIGN_SYM (x, e) ->
	  ASSIGN_SYM (self#transformVar x,
		      self#transformSymExp e)
      | ASSIGN_STRUCT (x, y) ->
	  ASSIGN_STRUCT (self#transformVar x,
			 self#transformVar y)
      | ASSIGN_NUM_ELT (a, i, v) ->
	  ASSIGN_NUM_ELT (self#transformVar a,
			  self#transformVar i,
			  self#transformVar v)
      | ASSIGN_SYM_ELT (a, i, v) ->
	  ASSIGN_SYM_ELT (self#transformVar a,
			  self#transformVar i,
			  self#transformVar v)
      | READ_NUM_ELT (v, a, i) ->
	  READ_NUM_ELT (self#transformVar v,
			self#transformVar a,
			self#transformVar i)
      | READ_SYM_ELT (v, a, i) ->
	  READ_SYM_ELT (self#transformVar v,
			self#transformVar a,
			self#transformVar i)
      | SHIFT_ARRAY (tgt, src, n) ->
	  SHIFT_ARRAY (self#transformVar tgt,
		       self#transformVar src, n)
      |	BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
	  BLIT_ARRAYS (self#transformVar tgt,
		      self#transformVar tgt_o,
		      self#transformVar src,
		      self#transformVar src_o,
		      self#transformVar n)
      |	SET_ARRAY_ELTS (a, s, n, v) ->
	  SET_ARRAY_ELTS (self#transformVar a,
			  self#transformVar s,
			  self#transformVar n,
			  self#transformVar v)
      | ASSERT e ->
	  ASSERT (self#transformBoolExp e)
      | OPERATION {op_name = name; op_args = args} ->
	  let transformArg (s,v,m)  = (s, self#transformVar v, m) in
	  OPERATION {op_name = name;
		      op_args = List.map transformArg args}
      | DOMAIN_OPERATION (ds, {op_name = name; op_args = args}) ->
	  let transformArg (s,v,m)  = (s, self#transformVar v, m) in
	  DOMAIN_OPERATION (ds, {op_name = name;
				  op_args = List.map transformArg args})
      | DOMAIN_CMD (dom, c, args) ->
	  let transformArg a =
	    match a with
	    | VAR_DOM_ARG v -> VAR_DOM_ARG (self#transformVar v)
	    | _ -> a in
	  DOMAIN_CMD (dom, c, List.map transformArg args)
      |	BREAKOUT_BLOCK  _
      |	BREAK _
      |	GOTO_BLOCK _
      |	LABEL _
      |	GOTO _
      |	LOOP _
      | CALL _
      |	CONTEXT _
      |	DOMAINS _
      |	MOVE_VALUES _
      |	MOVE_RELATIONS _
      |	SELECT _
      |	INSERT _
      |	DELETE _
      | ASSIGN_TABLE _ ->
	  pr_debug [STR "command not supported "; command_to_pretty 0 cmd] ;
	  raise (JCH_failure
		   (LBLOCK [STR "command not supported ";
			     command_to_pretty 0 cmd]))
      |	_ -> super#transformCmd cmd

    method transformProcedure (proc:procedure_int):procedure_int  =
      let proc_name = proc#getName in
      let signature = proc#getSignature in
      let transformB (s, v) = (s, self#transformVar v) in
      let bindings = List.map transformB proc#getBindings in
      let scope = proc#getScope in
      let _ = scope#transformVariables self#transformVar in
      let body = proc#getBody in
      let _ = self#transformCode body in
      F.mkProcedure proc_name ~signature ~bindings ~scope ~body

    method transformSystem (system: system_int):system_int =
      let new_system = F.mkSystem system#getName in
      let procs = List.rev_map system#getProcedure system#getProcedures in
      let new_procs = List.rev_map self#transformProcedure procs in
      let _ = List.iter new_system#addProcedure new_procs in
      new_system

  end


class skip_and_code_remover_t =
  object (self: _)
    inherit code_transformer_t as super

    method !transformCode (code:code_int) =
      super#transformCode code ;
      code#removeSkips

    method !transformCmd
             (cmd:(code_int, cfg_int) command_t):(code_int, cfg_int) command_t =
      match cmd with
      |	CODE (s, code) ->
	  self#transformCode code ;
	  if code#length = 0 then
	    SKIP
	  else
	    CODE (s, code)
      |	TRANSACTION (s, code, None) ->
	  self#transformCode code ;
	  if code#length = 0 then
	    SKIP
	  else
	    TRANSACTION (s, code, None)
      |	_ ->
	  super#transformCmd cmd

    method transformProcedure (proc:procedure_int) =
      self#transformCode proc#getBody

    method transformSystem (system: system_int) =
      let procs = List.rev_map system#getProcedure system#getProcedures in
      List.iter self#transformProcedure procs

  end


let remove_skips_code_p (proc:procedure_int) =
  (new skip_and_code_remover_t)#transformProcedure proc


let remove_skips_code (system:system_int) =
  (new skip_and_code_remover_t)#transformSystem system

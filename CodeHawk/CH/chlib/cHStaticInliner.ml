(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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
  ------------------------------------------------------------------------------ *)

(* chlib *)
open CHCommon
open CHLanguage   
open CHNumerical
open CHPretty
open CHStack
open CHUtils

module Make (F: LANGUAGE_FACTORY) =
  struct
    
    class inlining_processor_t
            (depth: int)
            (expanded_proc: numerical_t SymbolCollections.table_t)
            ?(op_proc: op_processor_t option)
            (exclusions: symbol_t -> bool)
            (sys: system_int)
            (proc_scope: scope_int) =
    object (self: _)
         
      val context = []
                  
      val system = sys
                 
      val excludes = exclusions
                   
      val expanded = expanded_proc
                   
      val scope = proc_scope
                
      val depth = mkNumerical depth
                
      val op_processor = op_proc
                       
      inherit code_transformer_t as super
            
      method private inline p = 
        not(excludes p)
        && match expanded#get p with
	   | Some d -> d#lt depth
	   | None -> true
                   
      method transformCmd cmd =
        match cmd with
	| CONTEXT (s, code) ->
	   let processor' = {< context = s :: context >} in
	   let _ = processor'#expand code in
	   cmd
	| CALL (p, args) ->
	   if self#inline p then
	     let proc = system#getProcedure p in
	     let signature = proc#getSignature in
	     let bindings = proc#getBindings in
	     let actuals = new SymbolCollections.table_t in
	     let _ = List.iter (fun (param, arg) -> actuals#set param arg) args in
	     let formals = new SymbolCollections.table_t in
	     let _ = List.iter (fun (param, formal) -> formals#set param formal) bindings in
	     let get_formal param =
	       match formals#get param with
	       | None -> raise (CHFailure (LBLOCK [STR "Unknown parameter: "; param#toPretty]))
	       | Some f -> f
	     in
	     let get_arg param =
	       match actuals#get param with
	       | None -> raise (CHFailure (LBLOCK [STR "Unknown parameter: "; param#toPretty]))
	       | Some a -> a
	     in
	     let read rename param t =
	       let formal = rename (get_formal param) in
	       let arg = get_arg param in
	       match t with
	       | NUM_ARRAY_TYPE | SYM_ARRAY_TYPE | NUM_TMP_ARRAY_TYPE | SYM_TMP_ARRAY_TYPE ->
		  ASSIGN_ARRAY (formal, arg)
	       | NUM_VAR_TYPE | NUM_TMP_VAR_TYPE ->
		  ASSIGN_NUM (formal, NUM_VAR arg)
	       | SYM_VAR_TYPE | SYM_TMP_VAR_TYPE ->
		  ASSIGN_SYM (formal, SYM_VAR arg)
	       | STRUCT_TYPE _ ->
		  ASSIGN_STRUCT (formal, arg)
	       | NR_TABLE_TYPE _ ->
		  ASSIGN_TABLE (formal, arg)
	       | _ ->
		  raise (CHFailure (LBLOCK [STR "Unexpected type ";
                                            variable_type_to_pretty t; STR " in procedure call"]))
	     in
	     let write rename param t =
	       let formal = rename (get_formal param) in
	       let arg = get_arg param in
	       match t with
	       | NUM_ARRAY_TYPE | SYM_ARRAY_TYPE | NUM_TMP_ARRAY_TYPE | SYM_TMP_ARRAY_TYPE ->
		  ASSIGN_ARRAY (arg, formal)
	       | NUM_VAR_TYPE | NUM_TMP_VAR_TYPE ->
		  ASSIGN_NUM (arg, NUM_VAR formal)
	       | SYM_VAR_TYPE | SYM_TMP_VAR_TYPE ->
		  ASSIGN_SYM (arg, SYM_VAR formal)
	       | STRUCT_TYPE _ ->
		  ASSIGN_STRUCT (arg, formal)
	       | NR_TABLE_TYPE _ ->
		  ASSIGN_TABLE (arg, formal)
	       | _ ->
		  raise (CHFailure (LBLOCK [STR "Unexpected type ";
                                            variable_type_to_pretty t; STR " in procedure call"]))
	     in
	     let rec build rename l preamble postamble =
	       match l with
	       | [] ->
		  (preamble, postamble)
	       | (param, param_t, param_m) :: t ->
		  let (preamble', postamble') = 
		    match param_m with
		    | READ -> ((read rename param param_t) :: preamble, postamble)
		    | WRITE -> (preamble, (write rename param param_t) :: postamble)
		    | READ_WRITE ->
                       ((read rename param param_t)
                        :: preamble, (write rename param param_t) :: postamble)
		  in
		  build rename t preamble' postamble'
	     in
	     let rename = scope#mergeWith proc#getScope in
	     let abstract = [ABSTRACT_VARS (List.map (fun v -> rename v) proc#getScope#getVariables)] in
	     let (preamble, postamble) = build rename signature [] abstract in
	     let inlined =
               proc#getBody#clone
                 ?context:(Some context)
                 ?renaming:(Some rename)
                 ?op_proc:op_processor () in
	     let expanded' = expanded#clone in
	     let _ = match expanded#get p with
	       | None -> expanded'#set p numerical_one
	       | Some d -> expanded'#set p (d#add numerical_one)
	     in
	     let processor' = {< expanded = expanded' >} in
	     let _ = processor'#expand inlined in
	     let code_sym = new symbol_t "inlined" in
	     CODE (code_sym, 
		   F.mkCode (preamble @ ((CODE (code_sym, inlined)) :: postamble)))
	   else
	     cmd
	| _ ->
	   super#transformCmd cmd
	  
      method expand code =
        self#transformCode code
	
    end
      
    class static_inliner_t
            ?(depth = 1)
            ?(op_proc: op_processor_t option)
            ?(exclusions: (symbol_t -> bool) option)
            (sys: system_int) =
    object (self: _)
         
      val system = sys
                 
      val excludes = match exclusions with
        | None -> (fun _ -> false)
        | Some f -> f
	          
      method expandProcedure (p: symbol_t) =
        let proc = system#getProcedure p in
        let expanded = new SymbolCollections.table_t in
        let inliner = new inlining_processor_t depth expanded ?op_proc excludes system proc#getScope in
        let body' = proc#getBody#clone () in
        let _ = inliner#expand body' in
	proc#setBody body'
	
    end
      
  end
  

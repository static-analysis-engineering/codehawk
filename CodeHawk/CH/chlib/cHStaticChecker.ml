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
open CHUtils

class static_type_checker_t local_check sys scope =
object (self: _)
     
  val system = sys
             
  val mutable in_transaction = false
                             
  inherit code_walker_t as super
        
  val vars = 
    let s = new VariableCollections.set_t in
    let _ = s#addList scope#getVariables in
    s
    
  val num_tmp_vars = 
    let s = new VariableCollections.set_t in
    let _ = s#addList scope#getNumTmpVariables in
    s
    
  val sym_tmp_vars = 
    let s = new VariableCollections.set_t in
    let _ = s#addList scope#getSymTmpVariables in
    s
    
  method private error msg =
    raise (CHStaticCheck (LBLOCK msg))
    
  method private hasVariable (varList : CHUtils.VariableCollections.set_t) searchVar =
    let rec findVarInType searchPath (searchVarIn : variable_t) =
      match searchVarIn#getType with
      | STRUCT_TYPE st ->
         (match searchPath with 
          | [name] -> (searchVarIn#field name)#equal searchVar
          | first :: last -> findVarInType last (searchVarIn#field first)
	  | [] -> false)
      | _ -> false
    in
    if varList#has searchVar then true else
      varList#fold (fun myBool myVar -> myBool || (findVarInType (searchVar#getPath) myVar)) false
    
  method walkVar v =
    let err () =
      self#error [STR "Variable "; v#toPretty; STR " is undefined"]
    in
    match v#getType with
    | NUM_LOOP_COUNTER_TYPE ->
       raise (CHStaticCheck (LBLOCK [STR "Forbidden use of loop counter "; v#toPretty]))
    | NUM_TMP_VAR_TYPE | NUM_TMP_ARRAY_TYPE ->
       if self#hasVariable num_tmp_vars v then
	 if in_transaction then
	   ()
	 else
	   raise (CHStaticCheck (LBLOCK [STR "Temporary variable "; v#toPretty;
                                         STR " used outside of a transaction"]))
       else
	 err ()
    | SYM_TMP_VAR_TYPE | SYM_TMP_ARRAY_TYPE ->
       if self#hasVariable sym_tmp_vars v then
	 if in_transaction then
	   ()
	 else
	   raise (CHStaticCheck (LBLOCK [STR "Temporary variable "; v#toPretty;
                                         STR " used outside of a transaction"]))
       else
	 err ()
    | _ ->
       if self#hasVariable vars v then
	 ()
       else
	 err ()
      
  method walkNumExp e =
    let error v =
      self#error [STR "Variable "; v#toPretty; STR " used in numerical expression"]
    in
    let _ = match e with
      | NUM_VAR v ->
	 if v#isNumerical && not(v#isArray) then
	   ()
	 else
	   error v
      | PLUS (x, y) | MINUS (x, y) | MULT (x, y) | DIV (x, y) ->
	 if x#isNumerical && not(x#isArray) then
	   ()
	 else
	   error x;
	 if y#isNumerical && not(y#isArray) then
	   ()
	 else
	   error y
      | _ ->
	 ()
    in
    super#walkNumExp e
    
  method walkSymExp e =
    let _ = match e with
      | SYM_VAR v ->
	 if v#isSymbolic && not(v#isArray) then
	   ()
	 else
	   self#error [STR "Variable "; v#toPretty; STR " used in symbolic expression"]
      | _ ->
	 ()
    in
    super#walkSymExp e
    
  method walkBoolExp e =
    let _ = match e with
      | LEQ (x, y)
        | GEQ (x, y)
        | LT (x, y)
        | GT (x, y)
        | EQ (x, y)
        | NEQ (x, y) ->
	 if x#isNumerical && not(x#isArray) then
	   ()
	 else
	   self#error [STR "Variable "; x#toPretty; STR " used in numerical predicate"];
	 if y#isNumerical && not(y#isArray) then
	   ()
	 else
	    self#error [STR "Variable "; y#toPretty; STR " used in numerical predicate"]
      | SUBSET (v, _)	  
      | DISJOINT (v, _) -> 
	 if v#isSymbolic && not(v#isArray) then
	   ()
	 else
	   self#error [STR "Variable "; v#toPretty; STR " used in symbolic predicate"]
      | _ ->
	 ()
    in
    super#walkBoolExp e
    
  method walkCmd cmd =
    match cmd with
    | TRANSACTION (_, code, post_code) ->
       let checker = object
	   inherit code_walker_t
	         
	   method walkCmd cmd =
	     match cmd with
	     | LOOP _
	       | CFG _ ->
		self#error [STR "No loop or CFG allowed inside a transaction"]
	     | TRANSACTION _ ->
		self#error [STR "No nested transactions"]
	     | _ ->
		self#walkCmd cmd
	       
	 end
       in
       in_transaction <- true;
       checker#walkCode code;
       begin
	 match post_code with
	 | None -> ()
	 | Some code -> checker#walkCode code
       end;
       in_transaction <- false
    | _ ->
       let _ = match cmd with
	 | CFG (_, cfg) ->
	    let states = cfg#getStatesFrom cfg#getEntry#getLabel in
	    let _ =
              if List.exists (fun s -> s#equal cfg#getExit#getLabel) states then
		()
	      else
		self#error [STR "The exit state of the CFG is unreachable"]
	    in
	    let _ =
              if cfg#getEntry#getIncomingEdges = [] then
		()
	      else
		self#error [STR "The entry state of a CFG must not have incoming edges"]
	    in
	    let _ =
              if cfg#getExit#getOutgoingEdges = [] then
		()
	      else
		self#error [STR "The exit state of a CFG must not have outgoing edges"]
	    in
	    super#walkCmd cmd
	 | ABSTRACT_ELTS (a, min, max) ->
	    if a#isArray then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in array abstraction"];
	    if min#isNumerical && not(min#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; min#toPretty; STR " used as numerical index"];
	    if max#isNumerical && not(max#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; max#toPretty; STR " used as numerical index"]	  
	 | ASSIGN_NUM (x, e) ->
	    self#walkNumExp e;
	    if x#isNumerical && not(x#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; x#toPretty; STR " used in numerical assignment"]
	 | INCREMENT (x, _) ->
	    if x#isNumerical && not(x#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; x#toPretty; STR " used in numerical increment"]	  
	 | ASSIGN_SYM (x, e) ->
	    self#walkSymExp e;
	    if x#isSymbolic && not(x#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; x#toPretty; STR " used in symbolic assignment"]
	 | ASSIGN_NUM_ELT (a, i, v) ->
	    if a#isNumerical && a#isArray then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in array assignment"];
	    if v#isNumerical && not(v#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; v#toPretty; STR " used in numerical array assignment"];
	    if i#isNumerical && not(i#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; i#toPretty; STR " used as array index"]
	 | ASSIGN_SYM_ELT (a, i, v) ->
	    if a#isSymbolic && a#isArray then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in array assignment"];
	    if v#isSymbolic && not(v#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in symbolic array assignment"];
	    if i#isNumerical && not(i#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; i#toPretty; STR " used as array index"]
	 | READ_NUM_ELT (v, a, i) ->
	    if a#isNumerical && a#isArray then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in numerical array access"];
	    if v#isNumerical && not(v#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; v#toPretty; STR " used in numerical array acess"];
	    if i#isNumerical && not(i#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; i#toPretty; STR " used as array index"]
	 | READ_SYM_ELT (v, a, i) ->
	    if a#isSymbolic && a#isArray then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in symbolic array access"];
	    if v#isSymbolic && not(v#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in symbolic array access"];
	    if i#isNumerical && not(i#isArray) then
	      ()
	    else
	      self#error [STR "Variable "; i#toPretty; STR " used as array index"]
	 | ASSIGN_ARRAY (x, y) ->
	    if x#isArray then
	      ()
	    else
	      self#error [STR "Variable "; x#toPretty; STR " used in array assignment"];
	    if y#isArray then
	      ()
	    else
	      self#error [STR "Variable "; y#toPretty; STR " used in array assignment"];
	    if (x#isNumerical && y#isNumerical) || (x#isSymbolic && y#isSymbolic) then
	      ()
	    else
	      self#error [STR "Incompatible array types in array assignment"]
	 | SHIFT_ARRAY (tgt, src, _) ->
	    if tgt#isArray then
	      ()
	    else
	      self#error [STR "Variable "; tgt#toPretty; STR " used in array copy"];
	    if src#isArray then
	      ()
	    else
	      self#error [STR "Variable "; src#toPretty; STR " used in array copy"];
	    if (tgt#isNumerical && src#isNumerical) || (tgt#isSymbolic && src#isSymbolic) then
	      ()
	    else
	      self#error [STR "Incompatible array types in array copy"]
	 | BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
	    if tgt_o#isNumerical
               && src_o#isNumerical
               && n#isNumerical
               && tgt_o#isAtomic
               && src_o#isAtomic
               && n#isAtomic then
	      ()
	    else
	      self#error [STR "Incorrect index types in array blit"];
	    if tgt#isArray then
	      ()
	    else
	      self#error [STR "Variable "; tgt#toPretty; STR " used in array blit"];
	    if src#isArray then
	      ()
	    else
	      self#error [STR "Variable "; src#toPretty; STR " used in array blit"];
	    if (tgt#isNumerical && src#isNumerical) || (tgt#isSymbolic && src#isSymbolic) then
	      ()
	    else
	      self#error [STR "Incompatible array types in array blit"]
	 | SET_ARRAY_ELTS (a, s, n, v) ->
	    if a#isArray then
	      ()
	    else
	      self#error [STR "Variable "; a#toPretty; STR " used in array initialization"];
	    if s#isNumerical && n#isNumerical && s#isAtomic && n#isAtomic then
	      ()
	    else
	      self#error [STR "Incorrect index types in array initialization"];
	    if v#isAtomic
               && ((a#isNumerical
                    && v#isNumerical) || (a#isSymbolic && v#isSymbolic)) then
	      ()
	    else
	      self#error [STR "Incompatible array and value types in array initialization"]
	 | ASSERT e ->
	    self#walkBoolExp e
	 | CALL (p, params) when not(local_check) ->
	    let _ =
              if system#hasProcedure p then
		()
	      else
		raise (CHStaticCheck (LBLOCK [STR "Procedure call: procedure ";
                                              p#toPretty; STR " does not exist"]))
	    in
	    let proc = system#getProcedure p in
	    let signature = proc#getSignature in
	    let table = new SymbolCollections.simple_table_t in
	    let _ = List.iter (fun (p, t, m) -> table#set p (t, m)) signature in
	    let seen_p = new SymbolCollections.set_t in
	    let seen_r_w = new VariableCollections.set_t in
	    List.iter (fun (param, arg) ->
		if seen_p#has param then
		  raise (CHStaticCheck (LBLOCK [STR "Procedure call: duplicate parameter ";
                                                param#toPretty; STR " in call to procedure ";
                                                p#toPretty]))
		else
		  begin
		    seen_p#add param;
		    match table#get param with
		    | None ->
		       self#error [STR "Procedure call: procedure "; p#toPretty;
                                   STR " has no parameter named "; param#toPretty]
		    | Some (t, m) ->
		       begin
			 if compatible_types arg#getType t then
			   ()
			 else
			   self#error [STR "Procedure call: argument "; arg#toPretty;
                                       STR " is incompatible with parameter "; 
				       param#toPretty; STR " of procedure "; p#toPretty];
			 match m with
			 | READ ->
			    ()
			 | _ ->
			    let _ =
                              if seen_r_w#has arg then
				self#error [STR "Procedure call: variable "; arg#toPretty;
                                            STR " of parameter ";
					    p#toPretty; STR " may only occur once in write mode"]
			      else
				()
			    in
			    seen_r_w#add arg
		       end
		  end
	      ) params
	 | _ ->
	    ()
       in
       super#walkCmd cmd
       
end
  
class static_checker_t (sys: system_int) =
object (self: _)
     
  val system = sys
             
  method checkProcedure ?(locally = true) p =
    let proc = system#getProcedure p in
    let body = proc#getBody in
    let scope = proc#getScope in
    let bindings = proc#getBindings in
    let signature = proc#getSignature in
    let table = new SymbolCollections.simple_table_t in
    let _ = List.iter (fun (p, t, _) -> table#set p t) signature in
    let checker = new static_type_checker_t locally system scope in
    let seen_p = new SymbolCollections.set_t in
    let seen_v = new VariableCollections.set_t in
    List.iter (fun (param, v) ->
	if seen_v#has v then
	  raise (CHStaticCheck (LBLOCK [STR "Duplicate binding of variable ";
                                        v#toPretty; 
					STR " for parameter "; param#toPretty;
                                        STR " in procedure "; p#toPretty]))
	else if seen_p#has param then
	  raise (CHStaticCheck (LBLOCK [STR "Duplicate definition of parameter ";
                                        param#toPretty; STR " in procedure ";
                                        p#toPretty]))
	else
	  begin
	    seen_v#add v;
	    seen_p#add param;
	    match table#get param with
	    | None -> 
	       raise (CHStaticCheck (LBLOCK [STR "Unknown parameter "; param#toPretty; 
					     STR " in procedure "; p#toPretty]))
	    | Some t ->
	       if v#getType = t then
		 ()
	       else
		 raise (CHStaticCheck (LBLOCK [STR "Incompatible types in binding ";
                                               param#toPretty;
					       STR " => "; v#toPretty;
					       STR " in procedure "; p#toPretty]))
	  end
      ) bindings;
    if List.length bindings != table#size then
      raise (CHStaticCheck (LBLOCK [STR "Unbound parameters in procedure "; p#toPretty]))
    else
      ();
    try 
      checker#walkCode body
    with
    | CHStaticCheck msg ->
       raise (CHStaticCheck (LBLOCK [msg; STR " in procedure "; p#toPretty]))
      
  method checkAll =
    List.iter (self#checkProcedure ~locally:false) system#getProcedures
    
end
  
  

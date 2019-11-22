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

class code_t 
        (code_id: int) 
        ?(command_to_pretty=(CHLanguage.command_to_pretty 0))
        (l: ((code_int, cfg_int) command_t) list): code_int =
object (self: _)
     
  val id = code_id
         
  val mutable seq = Array.of_list l
                  
  method getId = id
               
  method toPretty = 
    LBLOCK [STR "{"; NL;
	    INDENT (tab, 
		    ABLOCK (Array.map 
			      (fun (cmd:((code_int,cfg_int) command_t)) -> 
				LBLOCK [command_to_pretty cmd; STR ";"; NL]) seq));
	    STR "}"]
    
  method length = Array.length seq
                
  method getCmdAt i = 
    try
      seq.(i)
    with
    | Invalid_argument _ ->
       raise (CHFailure (LBLOCK [STR "Command in code out of bounds: "; INT i]))
      
  method setCmdAt i cmd =
    try
      seq.(i) <- cmd
    with
    | Invalid_argument _ ->
       raise (CHFailure (LBLOCK [STR "Command in code out of bounds: "; INT i]))
      
  method clone
           ?(context = [])
           ?(renaming: (variable_t -> variable_t) option)
           ?(op_proc: op_processor_t option) () =
    let rename_num_exp f e =
      match e with
      | NUM _ -> e
      | NUM_VAR v -> NUM_VAR (f v)
      | PLUS (x, y) -> PLUS (f x, f y)
      | MINUS (x, y) -> MINUS (f x, f y)
      | MULT (x, y) -> MULT (f x, f y)
      | DIV (x, y) -> DIV (f x, f y)
    in
    let rename_sym_exp f e =
      match e with
      | SYM _ -> e
      | SYM_VAR v -> SYM_VAR (f v)
    in
    let rename_bool_exp f e =
      match e with
      | RANDOM -> e
      | TRUE -> e
      | FALSE -> e
      | LEQ (x, y) -> LEQ (f x, f y)
      | GEQ (x, y) -> GEQ (f x, f y)
      | LT (x, y) -> LT (f x, f y)
      | GT (x, y) -> GT (f x, f y)
      | EQ (x, y) -> EQ (f x, f y)
      | NEQ (x, y) -> NEQ (f x, f y)
      | SUBSET (x, s) -> SUBSET (f x, s)
      | DISJOINT (x, s) -> DISJOINT (f x, s)
    in
    let l = Array.length seq in
    let seq' = Array.copy seq in
    let _ = for i = 0 to l - 1 do
              let cmd = seq.(i) in
	      match cmd with
	      | CODE (s, code) ->
	         seq'.(i) <- CODE (s, code#clone ?context:(Some context) ?renaming ?op_proc ())
	      | CFG (s, cfg) ->
	         seq'.(i) <- CFG (s, cfg#clone ?context:(Some context) ?renaming ?op_proc ())
	      | RELATION code ->
	         seq'.(i) <- RELATION (code#clone ?context:(Some context) ?renaming ?op_proc ())
	      | TRANSACTION (s, code, post_code) ->
	         seq'.(i) <- TRANSACTION (s, code#clone ?context:(Some context) ?renaming ?op_proc (), 
				          match post_code with 
					  | None -> None 
					  | Some code ->
                                             Some (code#clone ?context:(Some context)
                                                              ?renaming ?op_proc ()))
	      | BREAKOUT_BLOCK (s, code) ->
	         seq'.(i) <- BREAKOUT_BLOCK (s, (code#clone ?context:(Some context)
                                                            ?renaming ?op_proc ()))
	      | GOTO_BLOCK code ->
	         seq'.(i) <- GOTO_BLOCK (code#clone ?context:(Some context) ?renaming ?op_proc ())
	      | BRANCH cl ->
	         seq'.(i) <- BRANCH (List.map (fun c -> c#clone ?context:(Some context)
                                                                ?renaming ?op_proc ()) cl)
	      | LOOP (c1, c2, c3) ->
	         seq'.(i) <- LOOP (c1#clone ?context:(Some context) ?renaming ?op_proc (), 
				   c2#clone ?context:(Some context) ?renaming ?op_proc (), 
				   c3#clone ?context:(Some context) ?renaming ?op_proc ())
	      | CONTEXT (s, code) ->
	         seq'.(i) <- CONTEXT (s, code#clone ?context:(Some (s :: context))
                                                    ?renaming ?op_proc ())
	      | DOMAINS (doms, code) ->
	         seq'.(i) <- DOMAINS (doms, code#clone ?context:(Some context)
                                                       ?renaming ?op_proc ())
	      | _ ->
	         begin
		   match renaming with
		   | Some f ->
		      let cmd' =
			match cmd with
			| ABSTRACT_VARS vars -> 
			   ABSTRACT_VARS (List.map f vars)
			| ABSTRACT_ELTS (a, min, max) ->
			   ABSTRACT_ELTS (f a, f min, f max)
			| ASSIGN_NUM (x, e) ->
			   ASSIGN_NUM (f x, rename_num_exp f e)
			| ASSIGN_ARRAY (x, y) ->
			   ASSIGN_ARRAY (f x, f y)
			| INCREMENT (v, n) -> 
			   INCREMENT (f v, n)
			| ASSIGN_SYM (x, e) ->
			   ASSIGN_SYM (f x, rename_sym_exp f e)
			| ASSIGN_STRUCT (x, y) ->
			   ASSIGN_STRUCT (f x, f y)
			| ASSIGN_NUM_ELT (a, i, v) ->
			   ASSIGN_NUM_ELT (f a , f i, f v)
			| ASSIGN_SYM_ELT (a, i, v) ->
			   ASSIGN_SYM_ELT (f a , f i, f v)
			| READ_NUM_ELT (v, a, i) ->
			   READ_NUM_ELT (f v, f a, f i)
			| READ_SYM_ELT (v, a, i) ->
			   READ_SYM_ELT (f v, f a, f i)
			| SHIFT_ARRAY (tgt, src, n) ->
			   SHIFT_ARRAY (f tgt, f src, n)
			| BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
			   BLIT_ARRAYS (f tgt, f tgt_o, f src, f src_o, f n)
			| SET_ARRAY_ELTS (a, s, n, v) ->
			   SET_ARRAY_ELTS (f a, f s, f n, f v)
			| ASSERT e ->
			   ASSERT (rename_bool_exp f e)
			| OPERATION {op_name = op_name; op_args = op_args} ->
			   let op = {op_name = op_name;
				     op_args = List.map (fun (n, v, m) -> (n, f v, m)) op_args}
			   in
			   let cmd' =
			     match op_proc with
			     | Some p ->
				let renaming' = match renaming with
				  | Some r -> r
				  | None -> fun v -> v
				in
				OPERATION (p ~renaming:renaming' ~context:context ~operation:op)
			     | None -> OPERATION op
			   in
			   cmd'			      
			| DOMAIN_OPERATION (domains, {op_name = op_name; op_args = op_args}) ->
			   let op = {op_name = op_name;
				     op_args = List.map (fun (n, v, m) -> (n, f v, m)) op_args}
			   in
			   let cmd' =
			     match op_proc with
			     | Some p ->
				let renaming' = match renaming with
				  | Some r -> r
				  | None -> fun v -> v
				in
				DOMAIN_OPERATION (domains, (p ~renaming:renaming'
                                                              ~context:context
                                                              ~operation:op))
			     | None -> DOMAIN_OPERATION (domains, op)
			   in
			   cmd'			      
			| CALL (p, args) ->
			   CALL (p, List.map (fun (n, v) -> (n, f v)) args)
			| DOMAIN_CMD (d, c, l) ->
			   DOMAIN_CMD (d, c, List.map (fun a ->
						 match a with 
						 | VAR_DOM_ARG v -> VAR_DOM_ARG (f v)
						 | _ -> a ) l)
			| MOVE_VALUES (vars, src, tgt) ->
			   MOVE_VALUES (List.map f vars, src, tgt)
			| MOVE_RELATIONS (vars, src, tgt) ->
			   MOVE_RELATIONS (List.map f vars, src, tgt)
			| SELECT {selected = selected; from = from; where = where} ->
			   SELECT {selected = List.map (fun (n, v) -> (n, f v)) selected;
				   from = f from;
				   where = List.map (fun (n, v) -> (n, f v)) where}
			| INSERT {into = into; values = values} ->
			   INSERT {into = f into;
				   values = List.map (fun (n, v) -> (n, f v)) values}
			| DELETE {rows_from = from; rows_where = where} ->
			   DELETE {rows_from = f from;
				   rows_where = List.map (fun (n, v) -> (n, f v)) where}
			| ASSIGN_TABLE (t1, t2) ->
			   ASSIGN_TABLE (f t1, f t2)
			| _ ->
			   cmd
		      in
		      seq'.(i) <- cmd'
		   | None ->
		      ()
	         end
            done
    in
    {< seq = seq' >}
    
  method removeSkips =
    let l = Array.to_list seq in
    seq <- Array.of_list (List.filter (fun cmd -> not(cmd = SKIP)) l)
    
end
  
class state_t (label: symbol_t) (code: code_int): state_int =
object (self: _)
     
  val label = label
            
  val code = code
           
  val incoming = new SymbolCollections.set_t
               
  val outgoing = new SymbolCollections.set_t
               
  method clone ?(context = []) ?renaming ?op_proc () =
    let code' = code#clone ?context:(Some context) ?renaming ?op_proc () in
    {< code = code' >}
    
  method getLabel = label
                  
  method getCode = code
                 
  method getIncomingEdges = incoming#toList
                          
  method getOutgoingEdges = outgoing#toList
                          
  method addIncomingEdge s =
    incoming#add s
    
  method addOutgoingEdge s =
    outgoing#add s
    
  method toPretty =
    LBLOCK [ label#toPretty; STR ": "; code#toPretty;
             STR " -> ";    
             pretty_print_list (self#getOutgoingEdges) (fun s -> s#toPretty) "[" "; " "]"
           ]
    
end
  
class cfg_t (cfg_id: int) (entry: symbol_t) (exit: symbol_t): cfg_int =
object (self: _)
     
  val id = cfg_id
         
  val states = new SymbolCollections.table_t
	     
  val entry = entry
            
  val exit = exit
           
  method getId = id

  method clone ?(context = []) ?renaming ?op_proc () =
    let entry' = ref self#getEntry in
    let exit' = ref self#getExit in
    let states' = new SymbolCollections.table_t in
    let _ =
      states#iter (fun name state ->
	  let state' = state#clone ?context:(Some context) ?renaming ?op_proc () in
	  let _ = if state#getLabel#equal entry then
		    entry' := state'
		  else if state#getLabel#equal exit then
		    exit' := state'
		  else
		    ()
	  in
	  states'#set name state') in
    {< states = states';
       entry = !entry'#getLabel;
       exit = !exit'#getLabel >}
    
  method getEntry = 
    match states#get entry with 
    | Some s -> s
    | _ -> 
       raise (CHFailure (LBLOCK [ STR "no state corresponding to entry label"]))
      
  method getExit = 
    match states#get exit with
    | Some s -> s
    | _ ->
       raise (CHFailure (LBLOCK [ STR "no state corresponding to exit label"]))
      
  method getState s =
    match states#get s with
    | None -> raise (CHFailure (LBLOCK [STR "State "; s#toPretty; STR " does not belong to CFG"]))
    | Some state -> state
	          
  method getStates = states#listOfKeys
                   
  method getStatesFrom (start: symbol_t) =
    let visited = new SymbolCollections.set_t in
    let rec traverse s acc =
      if visited#has s#getLabel then
	acc
      else
	let _ = visited#add s#getLabel in
	let acc' = s#getLabel :: acc in
	List.fold_left (fun a s -> traverse (self#getState s) a) acc' s#getOutgoingEdges
    in
    if states#has start then
      traverse self#getEntry []
    else
      raise (CHFailure (LBLOCK [STR "Unknown state "; start#toPretty; STR " in CFG"]))
    
  method addState s =
    states#set s#getLabel s
    
  method addStates l =
    List.iter (fun s -> states#set s#getLabel s) l
    
  method addEdge src tgt =
    let src_s = self#getState src in
    let tgt_s = self#getState tgt in
    begin
      src_s#addOutgoingEdge tgt;
      tgt_s#addIncomingEdge src
    end
    
  method private statesToPretty =
    let visited = new SymbolCollections.set_t in
    let rec traverse s acc =
      if visited#has s#getLabel then
	acc
      else
	let _ = visited#add s#getLabel in
	let acc' = (LBLOCK [s#toPretty; NL]) :: acc in
	List.fold_left (fun a s -> traverse (self#getState s) a) acc' s#getOutgoingEdges
    in
    let reachable = traverse self#getEntry [] in
    let all = new SymbolCollections.set_t in
    let _ = all#addList self#getStates in
    let unreachable = all#diff visited in
    LBLOCK [LBLOCK (List.rev reachable);
	    LBLOCK (List.map (fun s -> LBLOCK [(self#getState s)#toPretty; NL]) unreachable#toList)]
    
  method toPretty =
    LBLOCK [ STR "ENTRY: "; self#getEntry#getLabel#toPretty; NL;
             STR "EXIT: "; self#getExit#getLabel#toPretty; NL;
             self#statesToPretty
           ]
    
end
  
class scope_t ~tmp_base ~register_base =
object (self: 'a)
     
  val mutable max_available_suffix = 1
                                   
  val tmp_base_name = tmp_base
                    
  val register_base_name = new symbol_t register_base
                         
  val mutable vars = new VariableCollections.set_t
                   
  val num_tmp_vars = new VariableCollections.set_t
                   
  val sym_tmp_vars = new VariableCollections.set_t
                   
  val num_array_tmp_vars = new VariableCollections.set_t
                         
  val sym_array_tmp_vars = new VariableCollections.set_t
                         
  val mutable in_transaction = false
                             
  val mutable transaction_num_tmp = []
                                  
  val mutable transaction_sym_tmp = []
                                  
  val mutable transaction_num_array_tmp = []
                                        
  val mutable transaction_sym_array_tmp = []
                                        
  method getTmpBase = tmp_base 
                    
  method getRegisterBase = register_base
                         
  method getVariables = vars#toList 
                      
  method getNumTmpVariables = num_tmp_vars#toList 
                            
  method getSymTmpVariables = sym_tmp_vars#toList 
                            
  method getNumTmpArrays = num_array_tmp_vars#toList 
                         
  method getSymTmpArrays = sym_array_tmp_vars#toList 
                         
  method toPretty = 
    let pr l =
      INDENT (tab,
              LBLOCK (List.map (fun v ->
                          LBLOCK [v#toPretty; STR ": ";
                                  variable_type_to_pretty v#getType; NL]) l))
    in
    LBLOCK [ pr vars#toList;
	     pr num_tmp_vars#toList;
	     pr sym_tmp_vars#toList
           ]
    
  method addVariable v = vars#add v
                       
  method addVariables l = vars#addList l
                        
  method removeVariable v = vars#remove v
                          
  method removeVariables l = vars#removeList l
                           
  method transformVariables f =
    let new_vars = new VariableCollections.set_t in
    begin
      vars#iter (fun v -> new_vars#add (f v));
      vars <- new_vars
    end
    
  method private makeVariable (name: symbol_t) ?(register: bool option) (vtype: variable_type_t) =
    let v_0 = new variable_t name vtype in
    if vars#has v_0 then
      let v = new variable_t name ~suffix:max_available_suffix ?register vtype in
      let _ = max_available_suffix <- max_available_suffix + 1 in
      let _ = vars#add v in
      v
    else
      let _ = vars#add v_0 in
      v_0
      
  method mkVariable (name: symbol_t) (vtype: variable_type_t) =
    self#makeVariable name ~register:false vtype
    
  method mkRegister (vtype: variable_type_t) =
    self#makeVariable register_base_name ~register:true vtype
    
  method private renameVariable v table =
    if vars#has v then
      let v' = new variable_t v#getName ~suffix:max_available_suffix v#getType in
      begin
	max_available_suffix <- max_available_suffix + 1;
	vars#add v';
	table#set v v'
      end
    else
      begin
	vars#add v;
	table#set v v;
	if v#getSuffix < max_available_suffix then
          ()
        else
          max_available_suffix <- v#getSuffix + 1
      end
    
  method mergeWith (scope: 'a) =
    let l = scope#getVariables in
    let table = new VariableCollections.table_t in
    let _ = List.iter (fun v -> self#renameVariable v table) l in
    let _ = num_tmp_vars#addList scope#getNumTmpVariables in
    let _ = sym_tmp_vars#addList scope#getSymTmpVariables in
    let _ = num_array_tmp_vars#addList scope#getNumTmpArrays in
    let _ = sym_array_tmp_vars#addList scope#getSymTmpArrays in
    fun v ->
    match v#getType with
    | NUM_TMP_VAR_TYPE | SYM_TMP_VAR_TYPE 
      | NUM_TMP_ARRAY_TYPE | SYM_TMP_ARRAY_TYPE -> v
    | _ ->
       begin
	 match table#get v with
	 | None ->
            raise (CHFailure (LBLOCK [STR "Unknown variable "; v#toPretty; STR " in renaming"]))
	 | Some v' -> v'
       end
      
  method startTransaction =
    if in_transaction then
      raise (CHFailure (LBLOCK [STR "Transaction not complete"]))
    else
      begin
	in_transaction <- true;
	transaction_num_tmp <- num_tmp_vars#toList;
	transaction_sym_tmp <- sym_tmp_vars#toList;
	transaction_num_array_tmp <- num_array_tmp_vars#toList;
	transaction_sym_array_tmp <- sym_array_tmp_vars#toList
      end
    
  method endTransaction =
    if in_transaction then
      begin
	in_transaction <- false;
	transaction_num_tmp <- [];
	transaction_sym_tmp <- [];
	transaction_num_array_tmp <- [];
	transaction_sym_array_tmp <- []
      end
    else
      raise (CHFailure (LBLOCK [STR "Not in a transaction"]))
    
  method private mkNumTmpVar =
    let base = new symbol_t (tmp_base_name ^ "N") in
    let tmp = new variable_t base ~suffix:(num_tmp_vars#size + 1) NUM_TMP_VAR_TYPE in
    let _ = num_tmp_vars#add tmp in
    tmp
    
  method private mkSymTmpVar =
    let base = new symbol_t (tmp_base_name ^ "S") in
    let tmp = new variable_t base ~suffix:(sym_tmp_vars#size + 1) SYM_TMP_VAR_TYPE in
    let _ = sym_tmp_vars#add tmp in
    tmp
    
  method private mkNumTmpArray =
    let base = new symbol_t (tmp_base_name ^ "N") in
    let tmp = new variable_t base ~suffix:(num_array_tmp_vars#size + 1) NUM_TMP_ARRAY_TYPE in
    let _ = num_array_tmp_vars#add tmp in
    tmp
    
  method private mkSymTmpArray =
    let base = new symbol_t (tmp_base_name ^ "S") in
    let tmp = new variable_t base ~suffix:(sym_array_tmp_vars#size + 1) SYM_TMP_ARRAY_TYPE in
    let _ = sym_array_tmp_vars#add tmp in
    tmp
    
  method requestNumTmpVariable =
    if in_transaction then
      match transaction_num_tmp with
      | tmp :: l -> let _ = transaction_num_tmp <- l in tmp
      | [] -> self#mkNumTmpVar
    else
      raise (CHFailure (LBLOCK [STR "Temporary (N) can only be requested in a transaction"]))
    
  method requestSymTmpVariable =
    if in_transaction then
      match transaction_sym_tmp with
      | tmp :: l -> let _ = transaction_sym_tmp <- l in tmp
      | [] -> self#mkSymTmpVar
    else
      raise (CHFailure (LBLOCK [STR "Temporary (S) can only be requested in a transaction"]))
    
  method requestNumTmpArray =
    if in_transaction then
      match transaction_num_array_tmp with
      | tmp :: l -> let _ = transaction_num_tmp <- l in tmp
      | [] -> self#mkNumTmpArray
    else
      raise (CHFailure (LBLOCK [STR "Temporary (N) can only be requested in a transaction"]))
    
  method requestSymTmpArray =
    if in_transaction then
      match transaction_sym_array_tmp with
      | tmp :: l -> let _ = transaction_sym_tmp <- l in tmp
      | [] -> self#mkSymTmpArray
    else
      raise (CHFailure (LBLOCK [STR "Temporary (S) can only be requested in a transaction"]))
    
end
  
class procedure_t
        (name: symbol_t)
        (signature: signature_t)
        (bindings: bindings_t)
        (scope: scope_t)
        (body: code_t): procedure_int =
object
  
  val name = name
           
  val signature = signature
                
  val bindings = bindings
               
  val scope = scope
            
  val mutable body = body
                   
  method toPretty =
    LBLOCK [ STR "PROCEDURE "; name#toPretty; STR " ";
             signature_to_pretty signature; NL;
             INDENT (tab, 
	             LBLOCK [
		         STR "BINDINGS: "; bindings_to_pretty bindings; NL;
		         STR "SCOPE"; NL; scope#toPretty;
		         body#toPretty; NL
	            ])
           ]
    
  method getName = name
                 
  method getBody = body
                 
  method setBody b = body <- b
                   
  method getScope = scope
                  
  method getSignature = signature
                      
  method getBindings = bindings
                     
end
  
class system_t (name: symbol_t) =
object
  
  val name = name
           
  val table = new SymbolCollections.table_t
            
  method toPretty =
    LBLOCK (List.map (fun proc -> LBLOCK [proc#toPretty; NL]) table#listOfValues)
    
  method getName = name
                 
  method getProcedure name =
    match table#get name with
    | None -> raise (CHFailure (LBLOCK [STR "Procedure "; name#toPretty; STR " not found"]))
    | Some p -> p
	      
  method addProcedure (proc: procedure_t) =
    table#set proc#getName proc
    
  method getProcedures =
    table#listOfKeys
    
  method hasProcedure p = table#has p
                        
end
  
module LanguageFactory =
  struct
    
    let id_counter = ref 0
    let command_pretty_printer = ref (fun cmd -> command_to_pretty 0 cmd)
                               
    let set_command_pretty_printer f = command_pretty_printer := f
                                     
    let get_new_id () =
      let id = !id_counter + 1 in
      let _ = id_counter := id in
      id
      
    let mkCode cmds =
      new code_t (get_new_id ()) ~command_to_pretty:!command_pretty_printer cmds
      
    let mkState label code = new state_t label code
                           
    let mkCFG_s entry exit = new cfg_t (get_new_id ()) entry exit
                           
    let mkCFG entry exit =
      let cfg = new cfg_t (get_new_id ()) entry#getLabel exit#getLabel in
      begin
        cfg#addState entry;
        cfg#addState exit;
        cfg
      end
      
    let mkScope
          ?(tmp_base = "tmp")
          ?(register_base = "reg") () =
      new scope_t ~tmp_base:tmp_base ~register_base:register_base
      
    let mkProcedure name ~signature ~bindings ~scope ~body =
      new procedure_t name signature bindings scope body
      
    let mkSystem name = new system_t name 
                      
  end
  

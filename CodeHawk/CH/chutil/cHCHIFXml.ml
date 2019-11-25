(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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
open CHUtils

(* chutil *)
open CHLogger   
open CHXmlDocument

module H = Hashtbl


let variable_type_mapping = [
  (NUM_LOOP_COUNTER_TYPE, "NLCT") ;
  (NUM_TMP_VAR_TYPE     , "NTVT") ;
  (SYM_TMP_VAR_TYPE     , "STVT") ;
  (NUM_TMP_ARRAY_TYPE   , "NTAT") ;
  (SYM_TMP_ARRAY_TYPE   , "STAT") ;
  (NUM_VAR_TYPE         , "NVT" ) ;
  (SYM_VAR_TYPE         , "SVT" ) ;
  (NUM_ARRAY_TYPE       , "NAT" ) ;
  (SYM_ARRAY_TYPE       , "SAT" ) ]

let variable_type_strings = Hashtbl.create 11
let _ = List.iter
          (fun (vtt,str) ->
            H.add variable_type_strings vtt str) variable_type_mapping

let variable_type_to_string (variable_type:variable_type_t) =
  try
    H.find variable_type_strings variable_type
  with
    Not_found -> 
      begin
	ch_error_log#add
          "to-xml"
          (LBLOCK [ variable_type_to_pretty variable_type ; 
		    STR " not found" ]) ;
	raise (CHFailure (STR "variable_type_to_string"))
      end


let arg_mode_to_string (mode:arg_mode_t) =
  match mode with
  | READ -> "READ"
  | WRITE -> "WRITE"
  | READ_WRITE -> "READ_WRITE"

let symbol_def_to_xml (symbol:symbol_t) =
  let node = xmlElement "sym" in
  begin
    (if symbol#getSeqNumber = (-1) then
       ()
     else
       node#setIntAttribute "s" symbol#getSeqNumber) ;
    node#setAttribute "b" symbol#getBaseName ;
    node#appendChildren
      (List.map (fun a -> xml_string "attr" a) symbol#getAttributes) ;
    node
  end

let symbols = new SymbolCollections.set_t

let symbols_to_xml () =
  let node = xmlElement "symbols" in
  begin
    node#appendChildren (List.map (fun s -> symbol_def_to_xml s) symbols#toList) ;
    node
  end

let symbol_to_xml (symbol:symbol_t) =
  let _ = symbols#add symbol in
  let node = xmlElement "sym" in
  begin node#setIntAttribute "i" symbol#getIndex ; node end

let name_to_xml (name:symbol_t) = 
  let node = xmlElement "name" in
  begin
    node#appendChildren [ symbol_to_xml name ] ;
    node
  end

let numerical_to_xml (num:numerical_t) =
  let node = xmlElement "num" in
  begin node#setAttribute "v" num#toString ; node end

let rec variable_type_to_xml (variable_type:variable_type_t) =
  let node = xmlElement "vt" in
  match variable_type with
  | NR_TABLE_TYPE _ -> 
     begin
       chlog#add "to-xml" (STR "NR_TABLE_TYPE not supported")  ; 
       node#setAttribute "v" "NTT" ;
       node
     end
  | STRUCT_TYPE fields -> 
     begin node#appendChildren [ struct_fields_to_xml fields ] ; node end
  | _ -> 
     begin
       node#setAttribute "v" (variable_type_to_string variable_type) ;
       node
     end
    
and struct_fields_to_xml (fields:(symbol_t * variable_type_t) list) =
  let node = xmlElement "struct" in
  begin
    node#appendChildren
      (List.map (fun (s,vt) ->
           let fieldNode = xmlElement "fld" in
           begin
	     fieldNode#appendChildren [ symbol_to_xml s ; variable_type_to_xml vt ] ;
	     fieldNode
           end) fields) ;
    node
  end
  
let variable_def_to_xml (var:variable_t) =
  let suffix = var#getSuffix in
  let isRegister = var#isRegister in
  let path_to_xml (path:symbol_t list) =
    let node = xmlElement "path" in
    begin
      node#appendChildren (List.map (fun s -> symbol_to_xml s) path) ;
      node
    end in
  let node = xmlElement "var" in
  begin
    node#setIntAttribute "i" var#getIndex ;
    node#appendChildren [
        symbol_to_xml var#getName ; variable_type_to_xml var#getType ] ;
    (match var#getPath with
     | [] -> ()
     | p -> node#appendChildren [ path_to_xml p ]) ;
    (if suffix = 0 then () else node#setIntAttribute "suffix" var#getSuffix) ;
    (if isRegister then node#setYesNoAttribute "isreg" var#isRegister) ;
    node
  end
  
let variables = new VariableCollections.set_t
              
let variables_to_xml () =
  let node = xmlElement "vars" in
  begin
    node#appendChildren
      (List.map (fun v -> variable_def_to_xml v) variables#toList) ;
    node
  end
  
let variable_to_xml (var:variable_t) =
  let _ = variables#add var in
  let node = xmlElement "var" in
  begin node#setIntAttribute "i" var#getIndex ; node end
  
let domain_cmd_arg_to_xml (arg:domain_cmd_arg_t) =
  let node = xmlElement "dca" in
  match arg with
  | NUM_DOM_ARG num -> 
     begin node#appendChildren [ numerical_to_xml num ] ; node end
  | VAR_DOM_ARG var ->
     begin node#appendChildren [ variable_to_xml var ] ; node end
    
let numerical_exp_to_xml (exp:numerical_exp_t) =
  let node = xmlElement "nxp" in
  match exp with
  | NUM num -> 
     begin
       node#setAttribute "tg" "nm" ;
       node#setAttribute "v" num#toString ;
       node
     end
  | NUM_VAR var ->
     begin
       node#setAttribute "tg" "nv" ;
       node#setIntAttribute "v" var#getIndex ;
       node
     end
  | PLUS (v1,v2) | MINUS (v1,v2) | MULT (v1,v2) | DIV (v1,v2) ->
     let tag = match exp with
       | PLUS _ -> "p"
       | MINUS _ -> "m"
       | MULT _ -> "x"
       | DIV _ -> "d"
       | _ -> "xx" in
     begin 
       node#setAttribute "tg" tag ; 
       node#setIntAttribute "v1" v1#getIndex ;
       node#setIntAttribute "v2" v2#getIndex ;
       node
     end

let numerical_exp_to_attrs (node:xml_element_int) (exp:numerical_exp_t) =
  match exp with
  | NUM num ->
     begin
       node#setAttribute "nx" "nm" ;
       node#setAttribute "v" num#toString
     end
  | NUM_VAR var ->
     begin
       node#setAttribute "nx" "nv" ;
       node#setIntAttribute "v" var#getIndex
     end
  | PLUS (v1,v2) | MINUS (v1,v2) | MULT (v1,v2) | DIV (v1,v2) ->
     let tag =
       match exp with
       | PLUS _ -> "p"
       | MINUS _ -> "m"
       | MULT _ -> "x"
       | DIV _ -> "d"
       | _ -> "xx" in
    begin 
      node#setAttribute "nx" tag ;
      node#setIntAttribute "v1" v1#getIndex ;
      node#setIntAttribute "v2" v2#getIndex
    end

let symbolic_exp_to_xml (exp:symbolic_exp_t) =
  let node = xmlElement "sxp" in
  let make (tag:string) (l:xml_element_int list) =
    let n = xmlElement tag in
    begin
      n#appendChildren l ;
      node#appendChildren [ n ] ;
      node
    end in
  match exp with
  | SYM sym -> make "SYM" [ symbol_to_xml sym ]
  | SYM_VAR var -> make "SV" [ variable_to_xml var ]
                 
let boolean_exp_to_xml (exp:boolean_exp_t) =
  let node = xmlElement "bxp" in
  let make (tag:string) (v1:variable_t) (v2:variable_t) =
    let n = xmlElement tag in 
    begin 
      n#appendChildren [ variable_to_xml v1 ; variable_to_xml v2 ] ; 
      node#appendChildren [n] ; 
      node 
    end in
  let make_s (tag:string) (v:variable_t) (l:symbol_t list) =
    let n = xmlElement tag in
    begin
      n#appendChildren ((variable_to_xml v) :: (List.map (fun s -> symbol_to_xml s) l)) ;
      node#appendChildren [ n ] ;
      node
    end in
  match exp with
  | TRUE -> begin node#setAttribute "v" "t" ; node end
  | FALSE -> begin node#setAttribute "v" "f" ; node end
  | RANDOM -> begin node#setAttribute "v" "r" ; node end
  | LEQ (v1,v2) -> make "leq" v1 v2 
  | GEQ (v1,v2) -> make "geq" v1 v2
  | LT (v1,v2) -> make "lt" v1 v2
  | GT (v1,v2) -> make "gt" v1 v2
  | EQ (v1,v2) -> make "eq" v1 v2
  | NEQ (v1,v2) -> make "neq" v1 v2
  | SUBSET (v1,l) -> make_s "ss" v1 l
  | DISJOINT (v1,l) -> make_s "dj" v1 l
                     
let operation_to_xml (op:operation_t) =
  let node = xmlElement "op" in
  let args_to_xml l =
    let subNode = xmlElement "args" in
    begin
      subNode#appendChildren
        (List.map (fun (s,v,m) ->
	     let argNode = xmlElement "arg" in
	     begin
	       argNode#setAttribute "name" s ;
	       argNode#setAttribute "mode" (arg_mode_to_string m) ;
	       argNode#appendChildren [ variable_to_xml v ] ;
	       argNode
	     end ) l) ;
      subNode
    end in	  
  begin
    node#appendChildren [ symbol_to_xml op.op_name ; args_to_xml op.op_args ] ;
    node
  end
  
let signature_to_xml (signature:signature_t) =
  let node = xmlElement "signature" in
  begin
    node#appendChildren 
      (List.map (fun (sym,varty,argmode) ->
	   let subnode = xmlElement "formal" in
	   begin
	     subnode#appendChildren [ symbol_to_xml sym ; variable_type_to_xml varty ] ;
	     subnode#setAttribute "mode" (arg_mode_to_string argmode) ;
	     subnode
	   end) signature) ;
    node
  end
  
let bindings_to_xml (bindings:bindings_t) =
  let node = xmlElement "bindings" in
  begin
    node#appendChildren
      (List.map (fun (sym,var) ->
	   let subNode = xmlElement "bind" in
	   begin
	     subNode#appendChildren [ symbol_to_xml sym ; variable_to_xml var ] ;
	     subNode
	   end) bindings) ;
    node
  end
  
let scope_to_xml (scope:scope_int) =
  let node = xmlElement "scope" in
  let tmpBase = scope#getTmpBase in
  let registerBase = scope#getRegisterBase in
  let add_vars (tag:string) (vars:variable_t list) =
    match vars with
    | [] -> ()
    | _ ->
       let subNode = xmlElement tag in
       begin
	 subNode#appendChildren (List.map (fun v -> variable_to_xml v) vars) ;
	 node#appendChildren [ subNode ]
       end in
  begin
    (if tmpBase = "tmp" then () else node#setAttribute "tbase" tmpBase) ;
    (if registerBase = "reg" then () else node#setAttribute "rbase" registerBase) ;
    add_vars "vars" scope#getVariables ;
    add_vars "numtmps" scope#getNumTmpVariables ;
    add_vars "symtmps" scope#getSymTmpVariables ;
    add_vars "numarrs" scope#getNumTmpArrays ;
    add_vars "symarrs" scope#getSymTmpArrays ;
    node
  end
  
let rec code_to_xml (code:code_int) =
  let node = xmlElement "code" in
  let dummy = xmlElement "dummy" in
  let len = code#length in
  let arr = Array.make len dummy in
  begin
    node#setIntAttribute "id" code#getId ;
    for i = 0 to len - 1 do arr.(i) <- command_to_xml i (code#getCmdAt i) done ;
    node#appendChildren (Array.to_list arr) ;
    node
  end
  
and cfg_to_xml (cfg:cfg_int) =
  let node = xmlElement "cfg" in
  let states = List.map (fun s -> cfg#getState s) cfg#getStates in
  let states_to_xml =
    let subNode = xmlElement "states" in
    begin
      subNode#appendChildren (List.map (fun s -> state_to_xml s) states) ;
      subNode
    end in
  begin
    node#setIntAttribute "id" cfg#getId ;
    node#appendChildren
      [ symbol_to_xml cfg#getEntry#getLabel ;
        symbol_to_xml cfg#getExit#getLabel ; 
	states_to_xml ] ;
    node
  end
  
and state_to_xml (state:state_int) =
  let node = xmlElement "state" in
  let incoming_edges_to_xml =
    let subNode = xmlElement "incoming" in
    begin
      subNode#appendChildren (List.map (fun s -> symbol_to_xml s) state#getIncomingEdges) ;
      subNode
    end in
  let outgoing_edges_to_xml =
    let subNode = xmlElement "outgoing" in
    begin
      subNode#appendChildren (List.map (fun s -> symbol_to_xml s) state#getOutgoingEdges) ;
      subNode
    end in
  begin
    node#appendChildren
      [ symbol_to_xml state#getLabel ;
        code_to_xml state#getCode ;
	incoming_edges_to_xml ;
        outgoing_edges_to_xml ] ;
    node
  end
  
  
and command_to_xml (index:int) (cmd:(code_int,cfg_int) command_t):xml_element_int =
  let node = xmlElement "cmd" in
  let _ = node#setIntAttribute "index" index in
  let commandNode (tag:string) (subNodes: xml_element_int list) =
    let node = xmlElement tag in
    begin node#appendChildren subNodes ; node end in
  let args_to_xml l =
    let node = xmlElement "args" in
    begin
      node#appendChildren
        (List.map
           (fun (sym, var) ->
	     let subNode = xmlElement "arg" in
	     begin
	       subNode#appendChildren [ symbol_to_xml sym ; variable_to_xml var ] ;
	       subNode
	     end) l) ;
      node
    end in
  let subNode = match cmd with
      CODE (sym, code) -> commandNode "CODE" [ symbol_to_xml sym ; code_to_xml code ]
    | CFG (sym, cfg) -> commandNode "CFG" [ symbol_to_xml sym ; cfg_to_xml cfg ]
    | RELATION code -> commandNode "REL" [ code_to_xml code ]
    | TRANSACTION (sym,code,code_opt) ->
       begin
	 match code_opt with
	   Some code1 ->
           commandNode
             "TR" [ symbol_to_xml sym ; code_to_xml code ; code_to_xml code1 ]
	 | _ ->
            commandNode "TR" [ symbol_to_xml sym ; code_to_xml code ]
       end
    | BREAKOUT_BLOCK (sym,code) ->
       commandNode "BRKB" [ symbol_to_xml sym ; code_to_xml code ]
    | BREAK sym -> commandNode "BRK" [ symbol_to_xml sym ]
    | GOTO_BLOCK code -> commandNode "GTB" [ code_to_xml code ]
    | LABEL sym -> commandNode "LB" [ symbol_to_xml sym ]
    | GOTO sym -> commandNode "GT" [ symbol_to_xml sym ]
    | SKIP -> commandNode "SK" []
    | ABSTRACT_VARS vars ->
       commandNode "ABSV" (List.map (fun v -> variable_to_xml v) vars)
    | ASSIGN_NUM (var, exp) -> 
       let cmdNode = commandNode "ASGN" [] in
       let _ = cmdNode#setIntAttribute "lh" var#getIndex in
       let _ = numerical_exp_to_attrs cmdNode exp in
       cmdNode
    | INCREMENT (var, num) ->
       commandNode "INC" [ variable_to_xml var ; numerical_to_xml num ]
    | ASSIGN_SYM (var, exp) ->
       commandNode "ASGS" [ variable_to_xml var ; symbolic_exp_to_xml exp ]
    | ASSIGN_STRUCT (var1, var2) ->
       commandNode "ASGST" [ variable_to_xml var1 ; variable_to_xml var2 ]
    | ABSTRACT_ELTS (var1, var2, var3) ->
       commandNode "ABSE" [ variable_to_xml var1 ; variable_to_xml var2 ;
                            variable_to_xml var3 ]
    | ASSIGN_ARRAY (var1, var2) ->
       commandNode "ASGA" [ variable_to_xml var1 ; variable_to_xml var2 ]
    | ASSIGN_NUM_ELT (var1, var2, var3) ->
       commandNode "ASGNE" [ variable_to_xml var1 ; variable_to_xml var2 ;
                             variable_to_xml var3 ]
    | ASSIGN_SYM_ELT (var1, var2, var3) ->
       commandNode "ASGSE" [ variable_to_xml var1 ; variable_to_xml var2 ;
                             variable_to_xml var3 ]
    | READ_NUM_ELT (var1, var2, var3) ->
       commandNode "RNE" [ variable_to_xml var1 ; variable_to_xml var2 ;
                           variable_to_xml var3 ]
    | READ_SYM_ELT (var1, var2, var3) ->
       commandNode "RSE" [ variable_to_xml var1 ; variable_to_xml var2 ;
                           variable_to_xml var3 ]
    | SHIFT_ARRAY (var1, var2, num) -> 
       commandNode "SA" [ variable_to_xml var1 ; variable_to_xml var2 ;
                          numerical_to_xml num ]
    | BLIT_ARRAYS (var1, var2, var3, var4, var5) ->
       commandNode "BA" [ variable_to_xml var1 ; variable_to_xml var2 ;
                          variable_to_xml var3 ;
			  variable_to_xml var4 ; variable_to_xml var5 ]
    | SET_ARRAY_ELTS (var1, var2, var3, var4) ->
       commandNode "SAE" [ variable_to_xml var1 ; variable_to_xml var2 ;
                           variable_to_xml var3 ; variable_to_xml var4 ]
    | ASSERT exp -> commandNode "AST" [ boolean_exp_to_xml exp ]
    | BRANCH l -> commandNode "BR" (List.map (fun c -> code_to_xml c) l)
    | LOOP (c1,c2,c3) ->
       commandNode "LP" [ code_to_xml c1 ; code_to_xml c2 ; code_to_xml c3 ]
    | OPERATION op -> commandNode "OP" [ operation_to_xml op ]
    | DOMAIN_OPERATION (l,op) ->
       commandNode
         "DOP" 
	 ((operation_to_xml op) ::
            (List.map (fun s -> xml_attr_string "domain" "v" s) l))
    | CALL (sym, l) ->  commandNode "CL" ((symbol_to_xml sym) :: [ args_to_xml l])
    | CONTEXT (sym, code) ->
       commandNode "CTXT"  [ symbol_to_xml sym ; code_to_xml code ]
    | DOMAINS (l,code) ->
       commandNode
         "DOMS" 
         ((code_to_xml code ) :: (List.map (fun s -> xml_attr_string "dom" "v" s) l))
    | DOMAIN_CMD  (s1,s2,l)-> 
       let cmdNode = commandNode "DMCD" (List.map (fun a -> domain_cmd_arg_to_xml a) l) in
       let _ = cmdNode#setAttribute "s1" s1 in
       let _ = cmdNode#setAttribute "s2" s2 in
       cmdNode
    | MOVE_VALUES (l,s1,s2) ->
       let cmdNode = commandNode "MV" (List.map (fun v -> variable_to_xml v) l) in
       let _ = cmdNode#setAttribute "s1" s1 in
       let _ = cmdNode#setAttribute "s2" s2 in
       cmdNode
    | MOVE_RELATIONS (l,s1,s2) ->
       let cmdNode = commandNode "MR" (List.map (fun v -> variable_to_xml v) l) in
       let _ = cmdNode#setAttribute "s1" s1 in
       let _ = cmdNode#setAttribute "s2" s2 in
       cmdNode
    | SELECT _  | INSERT _ | DELETE _ | ASSIGN_TABLE _ ->
       begin
	 ch_error_log#add "to-xml" (STR "Encountered database operation") ;
	 raise (CHFailure (STR "Encountered database operation"))
       end in
  begin
    node#appendChildren [ subNode ] ;
    node
  end
  
  
let body_to_xml (code:code_int) =
  let node = xmlElement "body" in
  begin
    node#appendChildren [ code_to_xml code ] ;
    node
  end
  
let procedure_to_xml (proc:procedure_int) =
  let node = xmlElement "proc" in
  begin
    node#appendChildren [
        name_to_xml proc#getName ;
        signature_to_xml proc#getSignature ;
        bindings_to_xml proc#getBindings ;
        scope_to_xml proc#getScope ;
        body_to_xml proc#getBody ] ;
    node
  end    
  
let procedures_to_xml (system:system_int) =
  let node = xmlElement "procs" in
  begin
    node#appendChildren
      (List.map (fun p -> procedure_to_xml (system#getProcedure p)) system#getProcedures) ;
    node
  end
  
let system_to_xml (system:system_int) =
  let doc = xmlDocument () in
  let node = xmlElement "chif" in
  let procedures_in_xml = procedures_to_xml system in
  let variables_in_xml = variables_to_xml () in
  let symbols_in_xml = symbols_to_xml () in
  begin
    node#appendChildren
      [ name_to_xml system#getName ; procedures_in_xml ;
        symbols_in_xml ; variables_in_xml ] ;
    doc#setNode node ;
    doc
  end
  
  

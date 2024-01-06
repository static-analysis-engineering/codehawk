(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* cil *)
open GoblintCil

(* chutil *)
open CHXmlDocument

(* cchcil *)
open CHCilFunDeclarations
open CHCilSumTypeSerializer
open CHCilTypes

let cd = CHCilDictionary.cildictionary
let decls = CHCilDeclarations.cildeclarations


let write_xml_int_list ?(tag="r") (node: xml_element_int) (r: int list) =
  match r with
  | [] -> ()
  | _ -> node#setAttribute tag (String.concat "," (List.map string_of_int r))


let write_xml_string_list (node: xml_element_int) (l: string list) =
  match l with
  | [] -> ()
  | _ ->
     let indices = List.map cd#index_string l in
     node#setAttribute
       "str-indices"
       (String.concat "," (List.map string_of_int indices))


let write_xml_exp_list (node: xml_element_int) (l: exp list) =
  node#appendChildren (List.map (fun x ->
    let eNode = xmlElement "exp" in 
    begin
      cd#write_xml_exp eNode x;
      eNode
    end) l)


let rec write_xml_asm_output
          (node: xml_element_int)
          ((optName, konstraint, lval): (string option * string * lval)) =
  let set = node#setAttribute in
  begin
    cd#write_xml_lval node lval;
    set "constraint" konstraint;
    (match optName with Some name -> set "name" name | _ -> ())
  end


and write_xml_asm_output_list 
    (node: xml_element_int) (l: (string option * string * lval) list) =
  node#appendChildren (List.map (fun ao ->
    let aoNode = xmlElement "asmoutput" in 
    begin
      write_xml_asm_output aoNode ao;
      aoNode
    end) l)


and write_xml_asm_input 
    (node: xml_element_int)
    ((optName, konstraint, x): (string option * string * exp)) =
  let set = node#setAttribute in
  begin
    cd#write_xml_exp node x;
    set "constraint" konstraint;
    (match optName with Some name -> set "name" name | _ -> ())
  end


and write_xml_asm_input_list 
    (node: xml_element_int) (l: (string option * string * exp) list) =
  node#appendChildren (List.map (fun ai ->
    let aiNode = xmlElement "asminput" in 
    begin
      write_xml_asm_input aiNode ai;
      aiNode
    end) l)


and write_xml_label (node: xml_element_int) (label: label) =
  let set = node#setAttribute in
  let setb = node#setBoolAttribute in
  let _ = set "ltag" (label_mcts#ts label) in
  match label with
  | Label (lname, loc, programLabel) ->
    begin
      decls#write_xml_location node loc;
      set "lname" lname;
      setb "programlabel" programLabel
    end
  | Case (x,loc,_todo_col) ->
    begin
      cd#write_xml_exp node x;
      decls#write_xml_location node loc 
    end
  | CaseRange (xlo, xhi, loc, _todo_col) ->
    begin
      cd#write_xml_exp ~tag:"iexplo" node xlo;
      cd#write_xml_exp ~tag:"iexphi" node xhi;
      decls#write_xml_location node loc 
    end
  | Default (loc, _todo_col) -> decls#write_xml_location node loc


and write_xml_label_list (node: xml_element_int) (l: label list) =
  node#appendChildren
    (List.map (fun label ->
         let lNode = xmlElement "label" in 
         begin
           write_xml_label lNode label;
           lNode
         end) l)


and write_xml_instruction
    (fdecls: cilfundeclarations_int) (node: xml_element_int) (instr: instr) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  let _ = set "itag" (instr_mcts#ts instr) in
  match instr with
  | Set (lval, x, loc, _todo_col) ->
    begin
      cd#write_xml_lval node lval;
      cd#write_xml_exp node x;
      decls#write_xml_location node loc
    end
  | Call (optLval, fx, args, loc, _todo_col) ->
    let argsNode = xmlElement "args" in
    begin
      cd#write_xml_exp node fx;
      decls#write_xml_location node loc;
      write_xml_exp_list argsNode args;
      append [argsNode];
      (match optLval with None -> () | Some lval -> cd#write_xml_lval node lval)
    end
  | VarDecl (v, loc) ->
     begin
       ignore (fdecls#index_local v);
       decls#write_xml_location node loc
     end
       
  | Asm (attr, templates, asmoutputs, asminputs, registerclobbers, loc) ->
    let add_list name l f =
      match l with
      | [] -> ()
      | _ ->
	 let lNode = xmlElement name in
         begin
           f lNode l;
           append [lNode]
         end in
    begin
      decls#write_xml_location node loc;
      cd#write_xml_attributes node attr;
      add_list "asminputs" asminputs write_xml_asm_input_list;
      add_list "asmoutputs" asmoutputs write_xml_asm_output_list;
      add_list "templates" templates write_xml_string_list;
      add_list "registerclobbers" registerclobbers write_xml_string_list 
    end				


and write_xml_instruction_list
    (fdecls: cilfundeclarations_int) (node: xml_element_int) (l: instr list) =
  node#appendChildren (List.map (fun instr ->
    let iNode = xmlElement "instr" in 
    begin
      write_xml_instruction fdecls iNode instr;
      iNode
    end) l)


and write_xml_stmtkind
    (fdecls: cilfundeclarations_int) (node: xml_element_int) (skind: stmtkind) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  let _ = set "stag" (stmtkind_mcts#ts skind) in
  match skind with
  | Instr instrs -> 
    let iNode = xmlElement "instrs" in 
    begin
      write_xml_instruction_list fdecls iNode instrs;
      append [iNode]
    end
  | Return (optX, loc) ->
    begin
      decls#write_xml_location node loc;
      match optX with 
      | None -> () 
      | Some x -> cd#write_xml_exp node x
    end
  | Goto (stmtRef, loc) ->
    begin
      decls#write_xml_location node loc;
      seti "stmtid" !stmtRef.sid
    end
  | ComputedGoto (x, loc) ->
    begin
      cd#write_xml_exp node x;
      decls#write_xml_location node loc 
    end
  | Break loc | Continue loc -> decls#write_xml_location node loc
  | If (x, ifblock, elseblock,loc,_todo_col) ->
    let ifNode = xmlElement "thenblock" in
    let elseNode = xmlElement "elseblock" in
    begin
      cd#write_xml_exp node x;
      write_xml_function_block fdecls ifNode ifblock;
      write_xml_function_block fdecls elseNode elseblock;
      decls#write_xml_location node loc;
      append [ifNode; elseNode]
    end
  | Switch (x, block, stmtlist, loc, _todo_col) ->
    let bNode = xmlElement "block" in
    let sNode = xmlElement "stmts" in
    begin
      cd#write_xml_exp node x;
      write_xml_function_block fdecls bNode block;
      write_xml_int_list sNode (List.map (fun s -> s.sid) stmtlist);
      decls#write_xml_location node loc;
      append [bNode; sNode]
    end
  | Loop (body, loc, _todo_col, optContinueStmt, optBreakStmt) ->
    let bNode = xmlElement "block" in
    begin
      write_xml_function_block fdecls bNode body;
      decls#write_xml_location node loc;
      node#appendChildren [bNode];
      (match optContinueStmt with
       | Some stmt -> seti "continuestmtid" stmt.sid
       | _ -> ());
      (match optBreakStmt with
       | Some stmt -> seti "breakstmtid" stmt.sid
       | _ -> ())
    end
  | Block b ->
    let bNode = xmlElement "block" in
    begin
      write_xml_function_block fdecls bNode b;
      append [bNode]
    end


and write_xml_statement
    (fdecls: cilfundeclarations_int) (node: xml_element_int) (stmt: stmt) =
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  let sNode = xmlElement "skind" in
  let succsNode = xmlElement "succs" in
  let predsNode = xmlElement "preds" in
  begin
    write_xml_stmtkind fdecls sNode stmt.skind;
    write_xml_int_list succsNode (List.map (fun s -> s.sid) stmt.succs);
    write_xml_int_list predsNode (List.map (fun s -> s.sid) stmt.preds);
    append [sNode; succsNode; predsNode];
    (match stmt.labels with
     | [] -> ()
     | l ->
      let lNode = xmlElement "labels" in
      begin
        write_xml_label_list lNode stmt.labels;
        append [lNode]
      end);
    seti "sid" stmt.sid
  end


and write_xml_statement_list
    (fdecls: cilfundeclarations_int) (node:xml_element_int) (l:stmt list) =
  node#appendChildren (List.map (fun stmt ->
    let sNode = xmlElement "stmt" in 
    begin
      write_xml_statement fdecls sNode stmt;
      sNode
    end) l)


and write_xml_function_block
    (fdecls: cilfundeclarations_int) (node: xml_element_int) (b: block) =
  let append = node#appendChildren in
  let sNode = xmlElement "bstmts" in
  begin
    write_xml_statement_list fdecls sNode b.bstmts ;
    append [sNode];
    match b.battrs with
    | [] -> ()
    | _ -> cd#write_xml_attributes node b.battrs
  end


and write_xml_function_definition
    (node: xml_element_int) (f: fundec) (filename: string) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  let varNode = xmlElement "svar" in
  let dNode = xmlElement "declarations" in
  let bNode = xmlElement "sbody" in
  let fdecls = mk_cilfundeclarations () in
  begin
    decls#write_xml_varinfo varNode f.svar;
    List.iteri (fun i v -> ignore (fdecls#index_formal v (i+1))) f.sformals;
    List.iter (fun v -> ignore (fdecls#index_local v))  f.slocals;
    fdecls#write_xml dNode;
    write_xml_function_block fdecls bNode f.sbody;
    append [varNode; dNode; bNode] ;
    set "filename" filename 
  end


let write_xml_global_type_definition
      (node: xml_element_int) (tinfo: typeinfo) (loc: location) =
  begin
    decls#write_xml_typeinfo node tinfo;
    decls#write_xml_location node loc;
  end


let write_xml_global_type_definitions (node: xml_element_int) (l: global list) =
  node#appendChildren 
    (List.map (fun g ->
      match g with
      | GType (tinfo, loc) -> 
	let gNode = xmlElement "gtype" in
	begin
          write_xml_global_type_definition gNode tinfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_type_definition_list"))
       (List.filter (fun g -> match g with GType _ -> true | _ -> false) l) )


let write_xml_global_comptag (node: xml_element_int) (cinfo: compinfo) (loc: location) = 
  begin
    decls#write_xml_compinfo node cinfo;
    decls#write_xml_location node loc;
  end


let write_xml_global_comptag_definitions (node: xml_element_int) (l: global list) =
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GCompTag (cinfo,loc) ->
	let gNode = xmlElement "gcomptag" in
	begin
          write_xml_global_comptag gNode cinfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_comptag_definition_list"))
       (List.filter (fun g -> match g with GCompTag _ -> true | _ -> false) l))


let write_xml_global_comptag_declarations (node: xml_element_int) (l: global list) = 
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GCompTagDecl (cinfo,loc) ->
	let gNode = xmlElement "gcomptagdecl" in
	begin
          write_xml_global_comptag gNode cinfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_comptag_declaration_list"))
       (List.filter
          (fun g -> match g with GCompTagDecl _ -> true | _ -> false) l))


let write_xml_global_enumtag
      (node: xml_element_int) (einfo: enuminfo) (loc: location) = 
  begin
    decls#write_xml_enuminfo node einfo;
    decls#write_xml_location node loc;
  end


let write_xml_global_enumtag_definitions
      (node: xml_element_int) (l: global list) = 
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GEnumTag (einfo,loc) ->
	let gNode = xmlElement "genumtag" in
	begin
          write_xml_global_enumtag gNode einfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_enumtag_definition_list"))
       (List.filter
          (fun g -> match g with GEnumTag _ -> true | _ -> false) l))


let write_xml_global_enumtag_declarations
      (node: xml_element_int) (l: global list) = 
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GEnumTagDecl (einfo,loc) ->
	let gNode = xmlElement "genumtagdecl" in
	begin
          write_xml_global_enumtag gNode einfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_enumtag_declaration_list"))
       (List.filter
          (fun g -> match g with GEnumTagDecl _ -> true | _ -> false) l))


let write_xml_global_var_definition 
    (node: xml_element_int) (vinfo: varinfo) (iinfo: initinfo) (loc: location) = 
  begin
    decls#write_xml_varinfo node vinfo;
    decls#write_xml_location node loc;
    match iinfo.init with
    | None -> ()
    | Some i -> decls#write_xml_init node i
  end
  

let write_xml_global_var_definitions (node: xml_element_int) (l: global list) = 
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GVar (vinfo,iinfo,loc) ->
	let gNode = xmlElement "gvar" in
	begin
          write_xml_global_var_definition gNode vinfo iinfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_var_definition_list"))
       (List.filter
          (fun g -> match g with GVar _ -> true | _ -> false) l))


let write_xml_global_var_declaration
      (node: xml_element_int) (vinfo: varinfo) (loc: location) = 
  begin
    decls#write_xml_varinfo node vinfo;
    decls#write_xml_location node loc 
  end


let write_xml_global_var_declarations (node: xml_element_int) (l: global list) = 
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GVarDecl (vinfo,loc) ->
	let gNode = xmlElement "gvardecl" in
	begin
          write_xml_global_var_declaration gNode vinfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_var_declarationn_list"))
       (List.filter
          (fun g -> match g with GVarDecl _ -> true | _ -> false) l))


let write_xml_function_declaration
      (node: xml_element_int) (f: fundec) (loc: location) =
  begin
    decls#write_xml_varinfo node f.svar;
    decls#write_xml_location node loc 
  end


let write_xml_function_declarations (node: xml_element_int) (l: global list) = 
  node#appendChildren
    (List.map (fun g ->
      match g with
      | GFun (f,loc) ->
	let gNode = xmlElement "gfun" in
	begin
          write_xml_function_declaration gNode f loc;
          gNode
        end
      | _ -> raise (Invalid_argument "function_declaration_list"))
       (List.filter
          (fun g -> match g with GFun _ -> true | _ -> false) l))       

let write_xml_global_asm (node:xml_element_int) (s:string) (loc:location) = ()

let write_xml_global_asm_list (node:xml_element_int) (l:global list) = () 


let write_xml_global_pragma (node:xml_element_int) (a:attribute) (loc:location) = ()

let write_xml_global_pragma_list (node:xml_element_int) (l:global list) = () 


let write_xml_global_text (node:xml_element_int) (s:string) = ()

let write_xml_global_text_list (node:xml_element_int) (l:global list) = ()


let write_xml_cfile (node:xml_element_int) (f:file) (filename:string) =
  let tables = [
      (write_xml_global_type_definitions, "global-type-definitions");
      (write_xml_global_comptag_definitions, "global-comptag-definitions");
      (write_xml_global_comptag_declarations, "global-comptag-declarations");
      (write_xml_global_enumtag_definitions, "global-enumtag-definitions");
      (write_xml_global_enumtag_declarations, "global-enumtag-declarations");
      (write_xml_global_var_definitions, "global-var-definitions");
      (write_xml_global_var_declarations, "global-var-declarations");
      (write_xml_function_declarations, "functions");
      (write_xml_global_asm_list, "global-assembly-statements");
      (write_xml_global_pragma_list, "global-pragmas");
      (write_xml_global_text_list, "global-text")
    ] in
  begin
    node#appendChildren
      (List.map (fun (wx,tag) ->
           let tnode = xmlElement tag in
           begin
             wx tnode f.globals;
             tnode
           end) tables) ;
    node#setAttribute "filename" filename
  end

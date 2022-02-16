(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchcil *)
open BCHCBasicTypes
open BCHBCFunDeclarations
open BCHBCSumTypeSerializer


let bcd = BCHBCDictionary.bcdictionary


let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [
        STR "Type ";
        STR name;
        STR " tag: ";
        STR tag;
        STR " not recognized. Accepted tags: ";
        pretty_print_list accepted (fun s -> STR s) "" ", " ""] in
  begin
    ch_error_log#add "serialization tag" msg;
    raise (CHFailure msg)
  end


let write_xml_string_list (node: xml_element_int) (l: string list) =
  match l with
  | [] -> ()
  | _ ->
     let indices = List.map bcd#index_string l in
     node#setAttribute
       "str-indices"
       (String.concat "," (List.map string_of_int indices))


let write_xml_exp_list (node: xml_element_int) (l: bexp_t list) =
  node#appendChildren (List.map (fun x ->
    let eNode = xmlElement "exp" in 
    begin
      bcd#write_xml_exp eNode x;
      eNode
    end) l)


let read_xml_exp_list (node: xml_element_int): bexp_t list =
  let getcc = node#getTaggedChildren in
  List.map bcd#read_xml_exp (getcc "exp")


let rec write_xml_asm_output
          (node: xml_element_int)
          ((optName, konstraint, lval): (string option * string * blval_t)) =
  let set = node#setAttribute in
  begin
    bcd#write_xml_lval node lval;
    set "constraint" konstraint;
    (match optName with Some name -> set "name" name | _ -> ())
  end


and write_xml_asm_output_list 
(node:xml_element_int) (l:(string option * string * blval_t) list) =
  node#appendChildren (List.map (fun ao ->
    let aoNode = xmlElement "asmoutput" in 
    begin
      write_xml_asm_output aoNode ao;
      aoNode
    end) l)


and write_xml_asm_input 
(node:xml_element_int)
((optName, konstraint, x): (string option * string * bexp_t)) =
  let set = node#setAttribute in
  begin
    bcd#write_xml_exp node x ;
    set "constraint" konstraint ;
    (match optName with Some name -> set "name" name | _ -> ())
  end


and write_xml_asm_input_list 
(node: xml_element_int) (l: (string option * string * bexp_t) list) =
  node#appendChildren (List.map (fun ai ->
    let aiNode = xmlElement "asminput" in 
    begin
      write_xml_asm_input aiNode ai;
      aiNode
    end) l)


and write_xml_label (node: xml_element_int) (label: blabel_t) =
  let set = node#setAttribute in
  let setb = node#setBoolAttribute in
  let _ = set "ltag" (label_mcts#ts label) in
  match label with
  | Label (lname,loc,programLabel) ->
    begin
      bcd#write_xml_location node loc;
      set "lname" lname;
      setb "programlabel" programLabel
    end
  | Case (x,loc) ->
    begin
      bcd#write_xml_exp node x;
      bcd#write_xml_location node loc 
    end
  | CaseRange (xlo,xhi,loc) ->
    begin
      bcd#write_xml_exp ~tag:"iexplo" node xlo;
      bcd#write_xml_exp ~tag:"iexphi" node xhi;
      bcd#write_xml_location node loc 
    end
  | Default loc -> bcd#write_xml_location node loc


and write_xml_label_list (node: xml_element_int) (l: blabel_t list) =
  node#appendChildren (List.map (fun label ->
    let lNode = xmlElement "label" in 
    begin
      write_xml_label lNode label;
      lNode
    end) l)


and write_xml_instruction (node: xml_element_int) (instr: binstr_t) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  let _ = set "itag" (instr_mcts#ts instr) in
  match instr with
  | Set (lval, x, loc) ->
    begin
      bcd#write_xml_lval node lval;
      bcd#write_xml_exp node x;
      bcd#write_xml_location node loc
    end
  | Call (optLval, fx, args, loc) ->
    let argsNode = xmlElement "args" in
    begin
      bcd#write_xml_exp node fx;
      bcd#write_xml_location node loc;
      write_xml_exp_list argsNode args;
      append [argsNode] ;
      (match optLval with None -> () | Some lval -> bcd#write_xml_lval node lval)
    end
  | VarDecl (varuse, loc) ->
     let (vname, vid) = varuse in
     begin
       set "vname" vname;
       seti "vid" vid;
       bcd#write_xml_location node loc
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
      bcd#write_xml_location node loc;
      bcd#write_xml_attributes node attr;
      add_list "asminputs" asminputs write_xml_asm_input_list;
      add_list "asmoutputs" asmoutputs write_xml_asm_output_list;
      add_list "templates" templates write_xml_string_list;
      add_list "registerclobbers" registerclobbers write_xml_string_list 
    end				


and write_xml_instruction_list (node: xml_element_int) (l: binstr_t list) =
  node#appendChildren (List.map (fun instr ->
    let iNode = xmlElement "instr" in 
    begin
      write_xml_instruction iNode instr;
      iNode
    end) l)


and write_xml_stmtkind (node: xml_element_int) (skind: bstmtkind_t) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  let _ = set "stag" (stmtkind_mcts#ts skind) in
  match skind with
  | Instr instrs -> 
    let iNode = xmlElement "instrs" in 
    begin
      write_xml_instruction_list iNode instrs;
      append [iNode]
    end
  | Return (optX, loc) ->
    begin
      bcd#write_xml_location node loc;
      match optX with 
      | None -> () 
      | Some x -> bcd#write_xml_exp node x
    end
  | Goto (stmtid, loc) ->
    begin
      bcd#write_xml_location node loc;
      seti "stmtid" stmtid
    end
  | ComputedGoto (x, loc) ->
    begin
      bcd#write_xml_exp node x;
      bcd#write_xml_location node loc 
    end
  | Break loc | Continue loc -> bcd#write_xml_location node loc
  | If (x, thenblock, elseblock, loc) ->
    let thenNode = xmlElement "thenblock" in
    let elseNode = xmlElement "elseblock" in
    begin
      bcd#write_xml_exp node x;
      write_xml_function_block thenNode thenblock;
      write_xml_function_block elseNode elseblock;
      bcd#write_xml_location node loc;
      append [thenNode; elseNode]
    end
  | Switch (x, block, stmtlist, loc) ->
    let bNode = xmlElement "block" in
    begin
      bcd#write_xml_exp node x;
      write_xml_function_block bNode block;
      node#setIntListAttribute "stmts" stmtlist;
      bcd#write_xml_location node loc;
      append [bNode]
    end
  | Loop (body, loc, optContinueStmtid, optBreakStmtid) ->
    let bNode = xmlElement "block" in
    begin
      write_xml_function_block bNode body;
      bcd#write_xml_location node loc;
      node#appendChildren [bNode];
      (match optContinueStmtid with
       | Some sid -> seti "continuestmtid" sid
       | _ -> ());
      (match optBreakStmtid with
       | Some sid -> seti "breakstmtid" sid
       | _ -> ())
    end
  | Block b ->
    let bNode = xmlElement "block" in
    begin
      write_xml_function_block bNode b;
      append [bNode]
    end
  (* currently not supported; only used in MSVC *)    
  | TryFinally _ | TryExcept _ -> () 


and write_xml_statement (node: xml_element_int) (stmt: bstmt_t) =
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  let sNode = xmlElement "skind" in
  begin
    write_xml_stmtkind sNode stmt.skind;
    node#setIntListAttribute "succs" stmt.succs;
    node#setIntListAttribute "preds" stmt.preds;
    append [sNode];
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


and write_xml_statement_list (node: xml_element_int) (l: bstmt_t list) =
  node#appendChildren (List.map (fun stmt ->
    let sNode = xmlElement "stmt" in 
    begin
      write_xml_statement sNode stmt;
      sNode
    end) l)


and write_xml_function_block (node: xml_element_int) (b: bblock_t) =
  let append = node#appendChildren in
  let sNode = xmlElement "bstmts" in
  begin
    write_xml_statement_list sNode b.bstmts ;
    append [sNode];
    match b.battrs with
    | [] -> ()
    | _ -> bcd#write_xml_attributes node b.battrs
  end


let rec read_xml_label (node: xml_element_int): blabel_t =
  let get = node#getAttribute in
  let getb = node#getBoolAttribute in
  let tag = get "ltag" in
  match tag with
  | "label" ->
     Label (get "lname", bcd#read_xml_location node, getb "programlabel")
  | "case" -> Case (bcd#read_xml_exp node, bcd#read_xml_location node)
  | "caserange" ->
     CaseRange
       (bcd#read_xml_exp ~tag:"iexplo" node,
        bcd#read_xml_exp ~tag:"iexphi" node,
        bcd#read_xml_location node)
  | "default" -> Default (bcd#read_xml_location node)
  | s -> raise_tag_error "blabel_t" s label_mcts#tags


and read_xml_label_list (node: xml_element_int): blabel_t list =
  let getcc = node#getTaggedChildren in
  List.map read_xml_label (getcc "label")


(* Asm is ignored here *)
and read_xml_instruction (node: xml_element_int): binstr_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let tag = get "itag" in
  match tag with
  | "set" ->
     Set
       (bcd#read_xml_lval node,
        bcd#read_xml_exp node,
        bcd#read_xml_location node)
  | "call" ->
     let argsnode = getc "args" in
     let optlval = if has "ilval" then Some (bcd#read_xml_lval node) else None in
     let args = read_xml_exp_list argsnode in
     Call (optlval, bcd#read_xml_exp node, args, bcd#read_xml_location node)
  | "asm" -> Asm ([], [], [], [], [], bcd#read_xml_location node)
  | s -> raise_tag_error "binstr_t" s instr_mcts#tags       


and read_xml_instruction_list (node: xml_element_int): binstr_t list =
  let getcc = node#getTaggedChildren in
  List.map read_xml_instruction (getcc "instr")


and read_xml_stmtkind (node: xml_element_int): bstmtkind_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let tag = get "stag" in
  match tag with
  | "instr" -> Instr (read_xml_instruction_list (getc "instrs"))
  | "return" ->
     let optx = if has "iexp" then Some (bcd#read_xml_exp node) else None in
     Return (optx, bcd#read_xml_location node)
  | "goto" -> Goto (geti "stmtid", bcd#read_xml_location node)
  | "computedgoto" ->
     ComputedGoto (bcd#read_xml_exp node, bcd#read_xml_location node)
  | "break" -> Break (bcd#read_xml_location node)
  | "continue" -> Continue (bcd#read_xml_location node)
  | "if" ->
     let thenblock = read_xml_function_block (getc "thenblock") in
     let elseblock = read_xml_function_block (getc "elseblock") in
     If (bcd#read_xml_exp node, thenblock, elseblock, bcd#read_xml_location node)
  | "switch" ->
     Switch
       (bcd#read_xml_exp node,
        read_xml_function_block (getc "block"),
        node#getIntListAttribute "stmts",
        bcd#read_xml_location node)
  | "loop" ->
     Loop
       (read_xml_function_block (getc "block"),
        bcd#read_xml_location node,
        (if has "continuestmtid" then Some (geti "continuestmtid") else None),
        (if has "breakstmtid" then Some (geti "breakstmtid") else None))
  | "block" ->
     Block (read_xml_function_block (getc "block"))
  | s -> raise_tag_error "bstmtkind_t" s stmtkind_mcts#tags
                                                                       
  
and read_xml_statement (node: xml_element_int): bstmt_t =
  let getc = node#getTaggedChild in
  let geti = node#getIntAttribute in
  let hasc = node#hasOneTaggedChild in
  {
    skind = read_xml_stmtkind (getc "skind");
    sid = geti "sid";
    succs = node#getIntListAttribute "succs";
    preds = node#getIntListAttribute "preds";
    labels =
      if hasc "labels" then
        read_xml_label_list (getc "labels")
      else
        []
  }


and read_xml_statement_list (node: xml_element_int): bstmt_t list =
  let getcc = node#getTaggedChildren in
  List.map read_xml_statement (getcc "stmt")


and read_xml_function_block (node: xml_element_int): bblock_t =
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  {
    bstmts = read_xml_statement_list (getc "bstmts");
    battrs = if has "iattrs" then bcd#read_xml_attributes node else []
  }


let write_xml_function_definition (node: xml_element_int) (f: bcfundec_t) =
  let append = node#appendChildren in
  let varNode = xmlElement "svar" in
  let dNode = xmlElement "declarations" in
  let bNode = xmlElement "sbody" in
  let fdecls = mk_bcfundeclarations () in
  begin
    bcd#write_xml_varinfo varNode f.bsvar;
    List.iteri (fun i v -> ignore (fdecls#index_formal v (i+1))) f.bsformals;
    List.iter (fun v -> ignore (fdecls#index_local v)) f.bslocals;
    fdecls#write_xml dNode;
    write_xml_function_block bNode f.bsbody;
    append [varNode; dNode; bNode]
  end


  
let read_xml_function_definition (node: xml_element_int): bcfundec_t =
  let getc = node#getTaggedChild in
  {
    bsvar = bcd#read_xml_varinfo (getc "svar");
    bsformals = [];
    bslocals = [];
    bsbody = read_xml_function_block (getc "sbody")
  }


let write_xml_global_type_definition
      (node: xml_element_int) (tinfo: btypeinfo_t) (loc: b_location_t) =
  begin
    bcd#write_xml_typeinfo node tinfo;
    bcd#write_xml_location node loc;
  end


let write_xml_global_type_definitions (node: xml_element_int) (l: bglobal_t list) =
  node#appendChildren 
    (List.map (fun g ->
      match g with
      | GType (tinfo,loc) -> 
	let gNode = xmlElement "gtype" in
	begin
          write_xml_global_type_definition gNode tinfo loc;
          gNode
        end
      | _ -> raise (Invalid_argument "global_type_definition_list"))
       (List.filter (fun g -> match g with GType _ -> true | _ -> false) l))


let write_xml_global_comptag
      (node: xml_element_int) (cinfo: bcompinfo_t) (loc: b_location_t) = 
  begin
    bcd#write_xml_compinfo node cinfo;
    bcd#write_xml_location node loc;
  end


let write_xml_global_comptag_definitions
      (node: xml_element_int) (l: bglobal_t list) =
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


let write_xml_global_comptag_declarations
      (node: xml_element_int) (l: bglobal_t list) = 
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
      (node: xml_element_int) (einfo: benuminfo_t) (loc: b_location_t) =
  begin
    bcd#write_xml_enuminfo node einfo;
    bcd#write_xml_location node loc;
  end


let write_xml_global_enumtag_definitions
      (node: xml_element_int) (l: bglobal_t list) =
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
       (List.filter (fun g -> match g with GEnumTag _ -> true | _ -> false) l))


let write_xml_global_enumtag_declarations
      (node: xml_element_int) (l: bglobal_t list) = 
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
      (node: xml_element_int)
      (vinfo: bvarinfo_t)
      (iinfo: binitinfo_t)
      (loc: b_location_t) =
  begin
    bcd#write_xml_varinfo node vinfo;
    bcd#write_xml_location node loc;
    match iinfo with
    | None -> ()
    | Some i -> bcd#write_xml_init node i
  end
  

let write_xml_global_var_definitions (node: xml_element_int) (l: bglobal_t list) =
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
       (List.filter (fun g -> match g with GVar _ -> true | _ -> false) l))


let write_xml_global_var_declaration
      (node: xml_element_int) (vinfo: bvarinfo_t) (loc: b_location_t) =
  begin
    bcd#write_xml_varinfo node vinfo;
    bcd#write_xml_location node loc
  end


let write_xml_global_var_declarations (node: xml_element_int) (l: bglobal_t list) =
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
       (List.filter (fun g -> match g with GVarDecl _ -> true | _ -> false) l))


let write_xml_function_declaration
      (node: xml_element_int) (f: bcfundec_t) (loc: b_location_t) =
  begin
    bcd#write_xml_varinfo node f.bsvar;
    bcd#write_xml_location node loc 
  end


let write_xml_function_declarations (node: xml_element_int) (l: bglobal_t list) =
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
       (List.filter (fun g -> match g with GFun _ -> true | _ -> false) l))       


let write_xml_global_asm (node: xml_element_int) (s:string) (loc: b_location_t) =
  ()

  
let write_xml_global_asm_list (node: xml_element_int) (l: bglobal_t list) = () 

                                                                          
let write_xml_global_pragma
      (node: xml_element_int) (a: b_attribute_t) (loc: b_location_t) = ()

                                                                     
let write_xml_global_pragma_list (node: xml_element_int) (l: bglobal_t list) = () 


let write_xml_global_text (node: xml_element_int) (s:string) = ()


let write_xml_global_text_list (node: xml_element_int) (l: bglobal_t list) = ()


let write_xml_bcfile (node: xml_element_int) (f: bcfile_t) (filename: string) =
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
      (List.map (fun (wx, tag) ->
           let tnode = xmlElement tag in
           begin
             wx tnode f.bglobals;
             tnode
           end) tables) ;
    node#setAttribute "filename" filename
  end

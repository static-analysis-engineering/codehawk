(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
   
(* chutil *)
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHDictionary
open CCHDeclarations
open CCHFunDeclarations
open CCHTypesToPretty
open CCHUtilities


exception Invalid_tag of string * string
exception Invalid_enumeration of string * string


let pr2s = CHPrettyUtil.pretty_to_string


let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations


let write_xml_symbol (node:xml_element_int) (s:symbol_t) =
  begin
    node#setAttribute "sname" s#getBaseName ;
    node#setIntAttribute "seqnr" s#getSeqNumber ;
    match s#getAttributes with
    | [] -> ()
    | attrs ->
       let aanode = xmlElement "attrs" in
       begin
         aanode#appendChildren (List.map (fun attr ->
                                    let anode = xmlElement "attr" in
                                    begin anode#setAttribute "name" attr ; anode end)
                                         attrs) ;
         node#appendChildren [ aanode ]
       end
  end

let write_xml_symbol_list ?(tag="sym") (node:xml_element_int) (lst:symbol_t list) =
  node#appendChildren (List.map (fun s ->
                           let snode = xmlElement tag in
                           begin write_xml_symbol snode s ; snode end) lst)
  

let read_xml_symbol (node:xml_element_int):symbol_t =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let sname = node#getAttribute "sname" in
  let seqnr = node#getIntAttribute "seqnr" in
  let atts =
    if hasc "attrs" then
      List.map (fun anode -> anode#getAttribute "name") ((getc "attrs")#getTaggedChildren "attr")
    else
      [] in
  new symbol_t ~atts ~seqnr sname

let read_xml_symbol_list ?(tag="sym") (node:xml_element_int):symbol_t list =
  List.map read_xml_symbol (node#getTaggedChildren tag)
   
let variable_type_to_string (t:variable_type_t) =
  match t with
  | SYM_VAR_TYPE -> "S"
  | NUM_VAR_TYPE -> "N"
  | _ ->
     raise (Invalid_argument ("variable_type_to_string: " ^ pr2s (variable_type_to_pretty t)))

let variable_type_from_string (s:string) =
  match s with
  | "S" -> SYM_VAR_TYPE
  | "N" -> NUM_VAR_TYPE
  | _ ->
     raise (Invalid_argument ("variable_type_from_string: " ^ s))

(* Only covers the subset of variable types used in the c analyzer *)
let write_xml_variable (node:xml_element_int) (v:variable_t) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  begin
    set "vname" v#getName#getBaseName ;
    set "vtype" (variable_type_to_string v#getType) ;
    seti "seqnr" v#getName#getSeqNumber
  end

let read_xml_variable (node:xml_element_int):variable_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let vname = get "vname" in
  let vtype = variable_type_from_string (get "vtype") in
  let seqnr = geti "seqnr" in
  new variable_t (new symbol_t ~seqnr vname) vtype


let write_xml_int_list ?(tag="r") (node:xml_element_int) (r:int list) =
  match r with
  | [] -> ()
  | _ -> node#setAttribute tag (String.concat "," (List.map string_of_int r))

let read_xml_int_list ?(tag="r") (node:xml_element_int) : int list =
  try
    if node#hasNamedAttribute tag then
      List.map int_of_string (nsplit ',' (node#getAttribute tag))
    else
      []
  with
    Failure _ ->
    raise (CCHFailure (LBLOCK [ STR "read_xml_int_list: int_of_string on " ;
                                STR (node#getAttribute tag) ]))

let read_xml_string_index_list (node:xml_element_int):int list =
  try
    if node#hasNamedAttribute "str-indices" then
      List.map int_of_string (nsplit ',' (node#getAttribute "str-indices"))
    else
      []
  with
    Failure _ ->
    raise (CCHFailure (LBLOCK [ STR "read_xml_string_index_list: int_of_string on " ;
                                STR (node#getAttribute "str-indices") ]))
     
let write_xml_fielduse (node:xml_element_int) (fuse:(string * int)) =
  begin
    node#setAttribute "fname" (fst fuse) ;
    node#setIntAttribute "ckey" (snd fuse) ;
  end

let read_xml_fielduse (node:xml_element_int) : fielduse =
  (node#getAttribute "fname", node#getIntAttribute "ckey")
  
let write_xml_varuse (node:xml_element_int) (vuse:(string * int)) =
  begin
    node#setAttribute "vname" (fst vuse) ;
    node#setIntAttribute "vid" (snd vuse)
  end

let read_xml_varuse (node:xml_element_int) : varuse =
  (node#getAttribute "vname", node#getIntAttribute "vid")

  
let rec read_xml_exp_list (node:xml_element_int) : exp list =
  List.map cd#read_xml_exp (node#getTaggedChildren "exp")

and read_xml_exp_option_list ?(tag="exp") (node:xml_element_int):exp option list =
  List.map cd#read_xml_exp_opt (node#getTaggedChildren tag)

and write_xml_exp_option_list ?(tag="exp") (node:xml_element_int) (optexps:exp option list) =
  node#appendChildren
    (List.map (fun optexp ->
         let enode = xmlElement tag in
         begin
           cd#write_xml_exp_opt enode optexp;
           enode
         end) optexps)

let read_xml_asm_output (node:xml_element_int) : asm_output_t =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let get_opt_string tag = if has tag then Some (get tag) else None in
  (get_opt_string "name", get "constraint", cd#read_xml_lval node)


let read_xml_asm_output_list (node:xml_element_int) : asm_output_t list =
  List.map read_xml_asm_output (node#getTaggedChildren "asmoutput")

let read_xml_asm_input (node:xml_element_int) : asm_input_t =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let get_opt_string tag = if has tag then Some (get tag) else None in
  (get_opt_string "name", get "constraint", cd#read_xml_exp node)

let read_xml_asm_input_list (node:xml_element_int) : asm_input_t list =
  List.map read_xml_asm_input (node#getTaggedChildren "asminput")


let read_xml_instruction (node:xml_element_int) : instr =
  let hasc = node#hasOneTaggedChild in
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let read_list tag reader = if hasc tag then reader (getc tag) else [] in
  match get "itag" with
  | "set" -> Set (cd#read_xml_lval node, cd#read_xml_exp node, cdecls#read_xml_location node)
  | "call" -> Call (cd#read_xml_lval_opt node, cd#read_xml_exp node, 
		    read_xml_exp_list (getc "args"), cdecls#read_xml_location node)
  | "asm" -> Asm (cd#read_xml_attributes node, 
		  read_list "templates" read_xml_string_index_list,
		  read_list "asmoutputs" read_xml_asm_output_list,
		  read_list "asminputs" read_xml_asm_input_list,
		  read_list "registerclobbers" read_xml_string_index_list,
		  cdecls#read_xml_location node)
  | s -> raise (Invalid_enumeration ("instruction", s))

let read_xml_label (node:xml_element_int) : label =
  let get = node#getAttribute in
  let get_bool = node#getBoolAttribute in
  match get "ltag" with
  | "label" ->
     Label (get "lname", cdecls#read_xml_location node, get_bool "programlabel")
  | "case" -> Case (cd#read_xml_exp node, cdecls#read_xml_location node)
  | "caserange" ->
     let explo = cd#read_xml_exp ~tag:"explo" node in
     let exphi = cd#read_xml_exp ~tag:"exphi" node in
     CaseRange (explo, exphi, cdecls#read_xml_location node)
  | "default" -> Default (cdecls#read_xml_location node)
  | s -> raise (Invalid_enumeration ("label", s))

let read_xml_label_list (node:xml_element_int) : label list =
  List.map read_xml_label (node#getTaggedChildren "label")

let read_xml_instruction_list (node:xml_element_int) : instr list =
  List.map read_xml_instruction (node#getTaggedChildren "instr")

let rec read_xml_function_block (node:xml_element_int) : block =
  let getc = node#getTaggedChild in
  { battrs = cd#read_xml_attributes node ;
    bstmts = read_xml_statement_list (getc "bstmts")
  }

and read_xml_statement_list (node:xml_element_int) : stmt list =
  List.map read_xml_statement (node#getTaggedChildren "stmt")

and read_xml_statement (node:xml_element_int) : stmt =
  let get_int = node#getIntAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let labels = if hasc "labels" then 
      read_xml_label_list (getc "labels") 
    else [] in
  { labels = labels ;
    skind = read_xml_stmtkind (getc "skind") ;
    succs = read_xml_int_list (getc "succs") ;
    preds = read_xml_int_list (getc "preds") ;
    sid = get_int "sid"
  }

and read_xml_stmtkind (node:xml_element_int) : stmtkind =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let get_int = node#getIntAttribute in
  let get_loc () = cdecls#read_xml_location node in
  let get_block tag = read_xml_function_block (getc tag) in
  let get_opt_int tag = 
    if has tag then Some (get_int tag) else None in
  match get "stag" with
  | "instr" -> Instr (read_xml_instruction_list (getc "instrs"))
  | "return" -> Return (cd#read_xml_exp_opt node, get_loc ())
  | "goto"-> Goto (get_int "stmtid", get_loc ())
  | "computedgoto" -> ComputedGoto ( cd#read_xml_exp node, get_loc ())
  | "break" -> Break (get_loc ())
  | "continue" -> Continue (get_loc ())
  | "if" -> If (cd#read_xml_exp node,
		get_block "thenblock",
		get_block "elseblock", get_loc ())
  | "switch" -> Switch (cd#read_xml_exp node, 
			get_block "block", 
			read_xml_int_list (getc "stmts"), 
			get_loc ())
  | "loop" -> Loop (get_block "block", get_loc (), 
		    get_opt_int "continuestmtid",
		    get_opt_int "breakstmtid")
  | "block" -> Block (get_block "block")
  (*	| "tryfinally" 
	| "tryexcept"              currently not supported *)
  | s -> raise (Invalid_enumeration ("statement kind", s))
    
let read_xml_function_definition (node:xml_element_int) : fundec =
  let getc = node#getTaggedChild in
  let fundecls = mk_cfundeclarations () in
  let _ = fundecls#read_xml (getc "declarations") in
  { svar = cdecls#read_xml_varinfo (getc "svar") ;
    sdecls = fundecls ;
    sbody = read_xml_function_block (getc "sbody")
  }

let read_xml_global_type_definition (node:xml_element_int) : global =
  GType (cdecls#read_xml_typeinfo node , cdecls#read_xml_location node)

let read_xml_global_type_definitions (node:xml_element_int) : global list =
  List.map read_xml_global_type_definition node#getChildren

let read_xml_global_comptag_definition (node:xml_element_int) : global =
  GCompTag (cdecls#read_xml_compinfo node, cdecls#read_xml_location node)

let read_xml_global_comptag_definitions (node:xml_element_int) : global list = 
  List.map read_xml_global_comptag_definition node#getChildren

let read_xml_global_comptag_declaration (node:xml_element_int) : global =
  GCompTagDecl (cdecls#read_xml_compinfo node, cdecls#read_xml_location node)

let read_xml_global_comptag_declarations (node:xml_element_int) : global list = 
  List.map read_xml_global_comptag_declaration node#getChildren

let read_xml_global_enumtag_definition (node:xml_element_int) : global =
  GEnumTag (cdecls#read_xml_enuminfo node, cdecls#read_xml_location node)
		
let read_xml_global_enumtag_definitions (node:xml_element_int) : global list = 
  List.map read_xml_global_enumtag_definition node#getChildren

let read_xml_global_enumtag_declaration (node:xml_element_int) : global =
  GEnumTagDecl (cdecls#read_xml_enuminfo node, cdecls#read_xml_location node)

let read_xml_global_enumtag_declarations (node:xml_element_int) : global list = 
  List.map read_xml_global_enumtag_declaration node#getChildren

let read_xml_global_var_definition (node:xml_element_int) : global =
  let init =
    if node#hasNamedAttribute "iinit" then
      Some (cdecls#read_xml_init node)
    else
      None in
  GVar (cdecls#read_xml_varinfo node, init, cdecls#read_xml_location node)

let read_xml_global_var_definitions (node:xml_element_int) : global list = 
  List.map read_xml_global_var_definition node#getChildren

let read_xml_global_var_declaration (node:xml_element_int) : global =
  GVarDecl (cdecls#read_xml_varinfo node, cdecls#read_xml_location node)

let read_xml_global_var_declarations (node:xml_element_int) : global list = 
  List.map read_xml_global_var_declaration node#getChildren 

let read_xml_function_declaration (node:xml_element_int) : global =
  GFun (cdecls#read_xml_varinfo node, cdecls#read_xml_location node)

let read_xml_function_declarations (node:xml_element_int) : global list = 
  List.map read_xml_function_declaration node#getChildren 
  
let read_xml_cfile (node:xml_element_int):file =
  let getc = node#getTaggedChild in
  let tables = [
      (read_xml_global_type_definitions, "global-type-definitions");
      (read_xml_global_comptag_definitions, "global-comptag-definitions");
      (read_xml_global_comptag_declarations, "global-comptag-declarations");
      (read_xml_global_enumtag_definitions, "global-enumtag-definitions");
      (read_xml_global_enumtag_declarations, "global-enumtag-declarations");
      (read_xml_global_var_definitions, "global-var-definitions");
      (read_xml_global_var_declarations, "global-var-declarations");
      (read_xml_function_declarations, "functions") ] in
  let globals = List.concat (List.map (fun (rx,tag) -> rx (getc tag)) tables) in
  {
    fileName = (node#getAttribute "filename") ^ ".c" ;
    globals = globals
  }

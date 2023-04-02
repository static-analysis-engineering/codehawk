(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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

(* cil *)
open GoblintCil

(* chlib *)
open CHPretty

(* chutil *)
open CHIndexTable
open CHStringIndexTable
open CHXmlDocument

(* cchcil *)
open CHCilSumTypeSerializer
open CHCilTypes

module H = Hashtbl


type funarg = string * typ * attributes


class cildictionary_t: cildictionary_int =
object (self)

  val attrparam_table = mk_index_table "attrparam-table"
  val attribute_table = mk_index_table "attribute-table"
  val attributes_table = mk_index_table "attributes-table"
  val constant_table = mk_index_table "constant-table"
  val exp_table = mk_index_table "exp-table"
  val funarg_table = mk_index_table "funarg-table"
  val funargs_table = mk_index_table "funargs-table"
  val lhost_table = mk_index_table "lhost-table"
  val lval_table = mk_index_table "lval-table"
  val offset_table = mk_index_table "offset-table"
  val typ_table = mk_index_table "typ-table"
  val typsig_table = mk_index_table "typsig-table"
  val typsiglist_table = mk_index_table "typsiglist-table"
  val string_table = mk_string_index_table "string-table"

  val mutable tables = []

  initializer
    begin
      tables <- [
        attrparam_table ;
        attribute_table ;
        attributes_table ;
        constant_table ;
        exp_table ;
        funarg_table ;
        funargs_table ;
        lhost_table ;
        lval_table ;
        offset_table ;
        typ_table ;
        typsig_table ;
        typsiglist_table ;
      ] ;
      ignore (offset_table#add (["n"],[])) ;
      ignore (attributes_table#add ([],[]))
    end
                       
  method index_attrparam (a:attrparam) =
    let tags = [ attrparam_mcts#ts a ] in
    let key = match a with
      | AInt i -> (tags, [i])
      | AStr s -> (tags, [self#index_string s])
      | ACons (s,r) -> (tags @ [s], List.map self#index_attrparam r)
      | ASizeOf typ -> (tags, [self#index_typ typ])
      | ASizeOfE a -> (tags, [self#index_attrparam a])
      | ASizeOfS s -> (tags, [self#index_typsig s])
      | AAlignOf typ -> (tags, [self#index_typ typ])
      | AAlignOfE a -> (tags, [self#index_attrparam a])
      | AAlignOfS s -> (tags, [self#index_typsig s])
      | AUnOp (unop,a) ->
         (tags @ [unop_mfts#ts unop], [self#index_attrparam a])
      | ABinOp (binop,a1,a2) ->
         (tags @ [binop_mfts#ts binop],
          [self#index_attrparam a1; self#index_attrparam a2])
      | ADot (a,s) -> (tags @ [s], [self#index_attrparam a])
      | AStar a -> (tags, [self#index_attrparam a])
      | AAddrOf a -> (tags, [self#index_attrparam a])
      | AIndex (a1,a2) ->
         (tags, [self#index_attrparam a1; self#index_attrparam a2])
      | AQuestion (a1, a2, a3) ->
         (tags,
          [self#index_attrparam a1;
           self#index_attrparam a2;
           self#index_attrparam a3]) in
    attrparam_table#add key

  method index_constant (c: constant):int =
    let tags = [constant_mcts#ts c] in
    let key = match c with
      | CInt (i64, ik, opts) ->
         (tags @ [Int64.to_string (GoblintCil.Cilint.int64_of_cilint i64); ikind_mfts#ts ik ], [])
      | CStr (s, _todo_encoding) -> (tags, [self#index_string s])
      | CWStr (i64r, _todo_encoding) -> (tags @ (List.map Int64.to_string i64r), [])
      | CChr c -> (tags, [Char.code c])
      | CReal (f, fk, opts) ->
         (tags
          @ [string_of_float f;
             fkind_mfts#ts fk;
             match opts with Some s -> s | _ -> "" ],
          [])
      | CEnum (exp, ename, iname) ->
         (tags @ [ename; iname.ename], [self#index_exp exp]) in
    constant_table#add key
    
  method index_lval ((lhost, offset): lval): int =
    lval_table#add ([], [self#index_lhost lhost; self#index_offset offset])

  method index_lhost (h: lhost): int =
    let key = match h with
    | Var vinfo -> (["var"; vinfo.vname], [vinfo.vid])
    | Mem exp -> (["mem"], [self#index_exp exp]) in
    lhost_table#add key

  method index_offset (offset: offset): int =
    let tags = [offset_mcts#ts offset] in
    let key = match offset with
      | NoOffset -> (tags, [])
      | Field (finfo, suboffset) ->
         (tags @ [finfo.fname], [finfo.fcomp.ckey; self#index_offset suboffset])
      | Index (exp,suboffset) ->
         (tags, [self#index_exp exp; self#index_offset suboffset]) in
    offset_table#add key

  method private index_opt_exp (x: exp option) =
    match x with Some e -> self#index_exp e | _ -> (-1)

  method private index_opt_exp_list (r: exp option list) =
    List.map self#index_opt_exp r

  method index_exp (exp: exp) =
    let tags = [exp_mcts#ts exp] in
    let key = match exp with
      | Const c -> (tags, [self#index_constant c])
      | Real exp -> (tags, [self#index_exp exp])
      | Imag exp -> (tags, [self#index_exp exp])
      | SizeOf typ -> (tags, [self#index_typ typ])
      | SizeOfE exp -> (tags, [self#index_exp exp])
      | SizeOfStr str -> (tags, [self#index_string str])
      | AlignOf typ -> (tags, [self#index_typ typ])
      | AlignOfE exp -> (tags, [self#index_exp exp])
      | Lval lval -> (tags,[self#index_lval lval])
      | UnOp (unop, exp, typ) ->
         (tags @ [unop_mfts#ts unop], [self#index_exp exp; self#index_typ typ])
      | BinOp (binop,exp1,exp2,typ) ->
         (tags @ [ binop_mfts#ts binop],
          [self#index_exp exp1; self#index_exp exp2; self#index_typ typ])
      | Question (exp1,exp2,exp3,typ) ->
         (tags,
          [self#index_exp exp1;
           self#index_exp exp2;
           self#index_exp exp3;
           self#index_typ typ])
      | CastE (typ,exp) ->
         (tags, [self#index_typ typ; self#index_exp exp])
      | AddrOf lval -> (tags, [self#index_lval lval])
      | AddrOfLabel stmtRef -> (tags, [!stmtRef.sid])
      | StartOf lval -> (tags, [self#index_lval lval]) in
    exp_table#add key

  method private index_attribute (a: attribute) =
    match a with
    | Attr (name, attrparams) ->
       attribute_table#add ([name], List.map self#index_attrparam attrparams)

  method private index_attributes (r: attributes) =
    attributes_table#add ([], List.map self#index_attribute r)

  method private index_funarg ((name, typ, attrs): funarg) =
    funarg_table#add ( [name], [self#index_typ typ; self#index_attributes attrs])

  method index_funargs (r: funarg list) =
    let r =
      List.mapi (fun i (name, typ, attrs) ->
          let name = if name = "" then "$par$" ^ (string_of_int (i+1)) else name in
          (name, typ, attrs)) r in
    funargs_table#add ([], List.map self#index_funarg r)
    
  method private index_opt_funargs (f: funarg list option) =
    match f with None -> (-1) | Some r -> self#index_funargs r

  method index_typ (typ: typ): int =
    (* omit entry for empty attributes *)
    let ia attrs = match attrs with
      | [] -> []
      | _ -> [self#index_attributes attrs] in
    let tags = [typ_mcts#ts typ ] in
    let key = match typ with
      | TVoid attrs -> (tags, ia attrs )
      | TInt (ik, attrs) -> (tags @ [ikind_mfts#ts ik], ia attrs)
      | TFloat (fk,attrs) -> (tags @ [fkind_mfts#ts fk], ia attrs)
      | TPtr (typ,attrs) -> (tags, (self#index_typ typ) :: ia attrs)
      | TArray (typ,optexp,attrs) ->
         (tags,
          [self#index_typ typ; self#index_opt_exp optexp] @ ia attrs)
      | TFun (typ,optfunargs,varargs,attrs) ->
         (tags,
          [self#index_typ typ;
           self#index_opt_funargs optfunargs;
           (if varargs then 1 else 0)] @ ia attrs)
      | TNamed (tinfo,attrs) -> (tags @ [tinfo.tname], ia attrs)
      | TComp (cinfo, attrs) -> (tags, (cinfo.ckey) :: ia attrs)
      | TEnum (einfo, attrs) -> (tags @ [einfo.ename], ia attrs)
      | TBuiltin_va_list attrs -> (tags, ia attrs) in                                       
    typ_table#add key

  method private index_opti64 (i64: int64 option): string =
    match i64 with Some i -> Int64.to_string i | _ -> ""

  method private index_typsig_list (tsigs: typsig list): int =
    typsiglist_table#add ([],List.map self#index_typsig tsigs)

  method private index_typsig_list_option (opttsigs: typsig list option): int =
    match opttsigs with Some tsigs -> self#index_typsig_list tsigs | _ -> (-1)

  method index_string (s: string) = string_table#add s

  method index_typsig (typsig: typsig): int =
    let tags = [ typsig_mcts#ts typsig ] in
    (* omit entry for empty attributes *)
    let ia attrs = match attrs with
      | [] -> []
      | _ -> [self#index_attributes attrs] in
    let key = match typsig with
      | TSArray (tsig, opti64, attrs) ->
         (tags @ [self#index_opti64 (Option.map GoblintCil.Cilint.int64_of_cilint opti64)],
          [self#index_typsig tsig] @ ia attrs)
      | TSPtr (tsig, attrs) -> (tags, (self#index_typsig tsig) :: ia attrs)
      | TSComp (b,s,attrs) -> (tags @ [s], (if b then 1 else 0) :: ia attrs)
      | TSFun (tsig,tsigs,b,attrs) ->
         (tags,
          [self#index_typsig tsig;
           self#index_typsig_list_option tsigs;
           (if b then 1 else 0)] @ ia attrs)
      | TSEnum (name,attrs) -> (tags @ [name], ia attrs)
      | TSBase typ -> (tags, [self#index_typ typ]) in
    typsig_table#add key

  method write_xml_attributes
           ?(tag="iattrs") (node: xml_element_int) (attr: attributes) =
    node#setIntAttribute tag (self#index_attributes attr)
       
  method write_xml_exp ?(tag="iexp") (node: xml_element_int) (exp: exp) =
    node#setIntAttribute tag (self#index_exp exp)

  method write_xml_funarg_list
           ?(tag="ifunargs") (node: xml_element_int) (r: funarg list) =
    node#setIntAttribute tag (self#index_funargs r)
    
  method write_xml_lval ?(tag="ilval") (node: xml_element_int) (lval: lval) =
    node#setIntAttribute tag (self#index_lval lval)

  method write_xml_offset
           ?(tag="ioffset") (node: xml_element_int) (offset: offset) =
    node#setIntAttribute tag (self#index_offset offset)

  method write_xml_typ ?(tag="ityp") (node: xml_element_int) (typ: typ) =
    node#setIntAttribute tag (self#index_typ typ)

  method write_xml_string ?(tag="istr") (node: xml_element_int) (s: string) =
    node#setIntAttribute tag (self#index_string s)

  method write_xml (node: xml_element_int) =
    let snode = xmlElement string_table#get_name in
    begin
      string_table#write_xml snode ;
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin t#write_xml tnode ; tnode end)
           tables) ;
      node#appendChildren [ snode ]
    end
end


let cildictionary = new cildictionary_t

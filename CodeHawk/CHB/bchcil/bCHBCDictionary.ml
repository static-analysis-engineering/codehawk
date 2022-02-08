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
open CHIndexTable
open CHLogger
open CHStringIndexTable
open CHXmlDocument

(* bchcil *)
open BCHCBasicTypes
open BCHBCSumTypeSerializer
open BCHCilTypes

module H = Hashtbl


let ibool b = if b then 1 else 0


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


class bcdictionary_t:bcdictionary_int =
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
  val location_table = mk_index_table "location-table"
  val varinfo_table = mk_index_table "varinfo-table"
  val initinfo_table = mk_index_table "initinfo-table"
  val offset_init_table = mk_index_table "offset-init-table"
  val fieldinfo_table = mk_index_table "fieldinfo-table"
  val compinfo_table = mk_index_table "compinfo-table"
  val enumitem_table = mk_index_table "enumitem-table"
  val enuminfo_table = mk_index_table "enuminfo-table"
  val typeinfo_table = mk_index_table "typeinfo-table"                     
  val tname_table = mk_index_table "tname-table"
  val tname_list_table = mk_index_table "tname-list-table"

  val mutable tables = []

  initializer
    begin
      tables <- [
        attrparam_table;
        attribute_table;
        attributes_table;
        constant_table;
        exp_table;
        funarg_table;
        funargs_table;
        lhost_table;
        lval_table;
        offset_table;
        typ_table;
        typsig_table;
        typsiglist_table;
        location_table;
        tname_table;
        tname_list_table;
        initinfo_table;
        offset_init_table;
        typeinfo_table;
        varinfo_table;
        fieldinfo_table;
        compinfo_table;
        enumitem_table;
        enuminfo_table
      ]
    end
                       
  method index_attrparam (a: b_attrparam_t) =
    let tags = [attrparam_mcts#ts a] in
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
         (tags @ [ unop_mfts#ts unop], [self#index_attrparam a])
      | ABinOp (binop,a1,a2) ->
         (tags @ [binop_mfts#ts binop],
          [self#index_attrparam a1; self#index_attrparam a2])
      | ADot (a,s) -> (tags @ [s], [self#index_attrparam a])
      | AStar a -> (tags, [self#index_attrparam a])
      | AAddrOf a -> (tags, [self#index_attrparam a])
      | AIndex (a1,a2) ->
         (tags, [self#index_attrparam a1; self#index_attrparam a2 ])
      | AQuestion (a1, a2, a3) ->
         (tags,
          [self#index_attrparam a1;
           self#index_attrparam a2;
           self#index_attrparam a3]) in
    attrparam_table#add key

  method private get_attrparam (index: int): b_attrparam_t =
    let name = "attrparam" in
    let (tags,args) = attrparam_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "aint" -> AInt (a 0)
    | "astr" -> AStr (self#get_string (a 0))
    | "acons" -> ACons ((t 1), List.map self#get_attrparam args)
    | "asizeof" -> ASizeOf (self#get_typ (a 0))
    | "asizeofe" -> ASizeOfE (self#get_attrparam (a 0))
    | "asizeofs" -> ASizeOfS (self#get_typsig (a 0))
    | "aalignof" -> AAlignOf (self#get_typ (a 0))
    | "aalignofe" -> AAlignOfE (self#get_attrparam (a 0))
    | "aalignofs" -> AAlignOfS (self#get_typsig (a 0))
    | "aunop" -> AUnOp (unop_mfts#fs (t 1), self#get_attrparam (a 0))
    | "abinop" ->
       ABinOp
         (binop_mfts#fs (t 1),
          self#get_attrparam (a 0),
          self#get_attrparam (a 1))
    | "adot" -> ADot (self#get_attrparam (a 0), (t 1))
    | "astar" -> AStar (self#get_attrparam (a 0))
    | "aaddrof" -> AAddrOf (self#get_attrparam (a 0))
    | "aindex" -> AIndex (self#get_attrparam (a 0), self#get_attrparam (a 1))
    | "aquestion" ->
       AQuestion
         (self#get_attrparam (a 0),
          self#get_attrparam (a 1),
          self#get_attrparam (a 2))
    | s -> raise_tag_error name s attrparam_mcts#tags

  method private index_opti64(i64: int64 option): string =
    match i64 with Some i -> Int64.to_string i | _ -> ""

  method private get_opti64 (s: string): int64 option =
    match s with "" -> None | _ -> Some (Int64.of_string s)
         
  method index_constant (c: bconstant_t):int =
    let tags = [constant_mcts#ts c] in
    let key = match c with
      | CInt64 (i64,ik, opts) ->
         (tags @ [Int64.to_string i64; ikind_mfts#ts ik], [])
      | CStr s -> (tags, [self#index_string s])
      | CWStr i64r -> (tags @ (List.map Int64.to_string i64r), [])
      | CChr c -> (tags, [ Char.code c ])
      | CReal (f,fk,opts) ->
         (tags @
            [string_of_float f;
             fkind_mfts#ts fk;
             match opts with Some s -> s | _ -> ""],
          [])
      | CEnum (exp, ename, iname) ->
         (tags @ [ ename; iname], [self#index_exp exp ]) in
    constant_table#add key

  method get_constant (index: int): bconstant_t =
    let name = "bconstant_t" in
    let (tags, args) = constant_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "int" ->
       CInt64 (Int64.of_string (t 1), ikind_mfts#fs (t 2),None)
    | "str" -> CStr (self#get_string (a 0))
    | "wstr" -> CWStr (List.map Int64.of_string (List.tl tags))
    | "chr" -> CChr (Char.chr (a 0))
    | "real" ->
       let t3 = if (List.length tags) > 3 then (t 3) else "" in
       CReal
         (float_of_string (t 1),
          fkind_mfts#fs (t 2),
          let s = t3 in if s = "" then None else Some s)
    | "enum" -> CEnum (self#get_exp (a 0), t 1, t 2)
    | s -> raise_tag_error name s constant_mcts#tags

  method index_opt_lval (l: blval_t option) =
    match l with Some lval -> self#index_lval lval | _ -> (-1)

  method get_opt_lval (index: int): blval_t option =
    if index = -1 then None else Some (self#get_lval index)
         
  method index_lval ((lhost, offset): blval_t):int =
    lval_table#add ([], [self#index_lhost lhost; self#index_offset offset])

  method get_lval (index: int): blval_t =
    let (_, args) = lval_table#retrieve index in
    match args with
    | [ lhostindex; offsetindex ] ->
       (self#get_lhost lhostindex, self#get_offset offsetindex)
    | _ ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "lval invalid format: ";
                 pretty_print_list args (fun i -> INT i) "[" ";" "]"]))
    
  method index_lhost (h: blhost_t):int =
    let key = match h with
    | Var (vname, vid) -> (["var"; vname], [vid])
    | Mem exp -> (["mem"], [self#index_exp exp]) in
    lhost_table#add key

  method get_lhost (index: int): blhost_t =
    let name = "blhost_t" in
    let (tags, args) = lhost_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "var" -> Var (t 1, a 0)
    | "mem" -> Mem (self#get_exp (a 0))
    | s -> raise_tag_error name s ["var"; "mem"]
    
  method index_offset (offset: boffset_t):int =
    let tags = [offset_mcts#ts offset] in
    let key = match offset with
      | NoOffset -> (tags, [])
      | Field ((fname, fckey), suboffset) ->
         (tags @ [fname], [fckey; self#index_offset suboffset])
      | Index (exp,suboffset) ->
         (tags, [self#index_exp exp; self#index_offset suboffset]) in
    offset_table#add key

  method get_offset (index: int): boffset_t =
    let name = "offset" in
    let (tags, args) = offset_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "n" -> NoOffset
    | "f" -> Field ((t 1, a 0), self#get_offset (a 1))
    | "i" -> Index (self#get_exp (a 0), self#get_offset (a 1))
    | s -> raise_tag_error name s offset_mcts#tags
    
  method private index_opt_exp (x: bexp_t option) =
    match x with Some e -> self#index_exp e| _ -> (-1)

  method private get_opt_exp (index:int) =
    if index = -1 then None else Some (self#get_exp index)
                                                
  method private index_opt_exp_list (r: bexp_t option list) =
    List.map self#index_opt_exp r

  method private get_opt_exp_list (r:int list) =
    List.map self#get_opt_exp r
    
  method index_exp (exp: bexp_t) =
    let tags = [exp_mcts#ts exp] in
    let key = match exp with
      | Const c -> (tags,[self#index_constant c])
      | SizeOf typ -> (tags,[self#index_typ typ])
      | SizeOfE exp -> (tags,[self#index_exp exp])
      | SizeOfStr str -> (tags, [self#index_string str])
      | AlignOf typ -> (tags, [self#index_typ typ])
      | AlignOfE exp -> (tags, [self#index_exp exp])
      | Lval lval -> (tags,[self#index_lval lval])
      | UnOp (unop,exp,typ) ->
         (tags @ [unop_mfts#ts unop],
          [self#index_exp exp; self#index_typ typ])
      | BinOp (binop,exp1,exp2,typ) ->
         (tags @ [binop_mfts#ts binop],
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
      | AddrOfLabel sid -> (tags, [sid])
      | StartOf lval -> (tags, [self#index_lval lval])
      | FnApp (loc, e, el) ->
         (tags,
          [self#index_location loc;
           self#index_exp e] @ (self#index_opt_exp_list el))
      | CnApp (s, el, t) ->
         (tags,
          [self#index_string s;
           self#index_typ t] @ (self#index_opt_exp_list el)) in
    exp_table#add key

  method get_exp (index: int): bexp_t =
    let name = "exp" in
    let (tags, args) = exp_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let suffixa n =
      let rec aux l n =
        match l with
        | [] -> []
        | _ -> if n <= 0 then l else aux (List.tl l) (n-1) in
      aux args n in
    match (t 0) with
    | "const" -> Const (self#get_constant (a 0))
    | "lval" -> Lval (self#get_lval (a 0))
    | "sizeof" -> SizeOf (self#get_typ (a 0))
    | "sizeofe" -> SizeOfE (self#get_exp (a 0))
    | "sizeofstr" -> SizeOfStr (self#get_string (a 0))
    | "alignof" -> AlignOf (self#get_typ (a 0))
    | "alignofe" -> AlignOfE (self#get_exp (a 0))
    | "unop" ->
       UnOp (unop_mfts#fs (t 1),self#get_exp (a 0), self#get_typ (a 1))
    | "binop" ->
       BinOp (binop_mfts#fs (t 1), self#get_exp (a 0), self#get_exp (a 1),
              self#get_typ (a 2))
    | "question" ->
       Question
         (self#get_exp (a 0),
          self#get_exp (a 1),
          self#get_exp (a 2),
          self#get_typ (a 3))
    | "caste" -> CastE (self#get_typ (a 0), self#get_exp (a 1))
    | "addrof" -> AddrOf (self#get_lval (a 0))
    | "addroflabel" -> AddrOfLabel (a 0)
    | "startof" -> StartOf (self#get_lval (a 0))
    | "fnapp" ->
       let loc = { file = (t 1); line = (a 0); byte = (a 1) } in
       let optexps = self#get_opt_exp_list (suffixa 3) in 
       FnApp (loc, self#get_exp (a 2), optexps)
    | "cnapp" ->
       let optexps = self#get_opt_exp_list (suffixa 1) in
       CnApp (t 1, optexps, self#get_typ (a 0))
    | s -> raise_tag_error name s exp_mcts#tags
    
  method private index_attribute (a: b_attribute_t) =
    match a with
    | Attr (name, attrparams) ->
       attribute_table#add ([name], List.map self#index_attrparam attrparams)

  method private get_attribute (index: int): b_attribute_t =
    let (tags, args) = attribute_table#retrieve index in
    if (List.length tags) > 0 then
      Attr (List.hd tags, List.map self#get_attrparam args)
    else
      raise (CHFailure (LBLOCK [STR "Attribute without a name"]))

  method private index_attributes (r: b_attributes_t) =
    attributes_table#add ([], List.map self#index_attribute r)

  method get_attributes (index:int) =
    if index = (-1) then
      []
    else
      let (_,args) = attributes_table#retrieve index in
      List.map self#get_attribute args    

  method private index_funarg ((name, typ, attrs): bfunarg_t) =
    funarg_table#add ([name], [self#index_typ typ; self#index_attributes attrs])

  method private get_funarg (index: int): bfunarg_t =
    let (tags,args) = funarg_table#retrieve index in
    if (List.length tags) > 0 && (List.length args) > 0 then
      let attrs =
        if (List.length args) > 1 then
          self#get_attributes (List.nth args 1)
        else
          [] in
      (List.hd tags, self#get_typ (List.hd args),attrs)
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Invalid funarg: ";
                STR "tags: ";
                pretty_print_list tags (fun s -> STR s) "[" "," "], ";
                STR "args: ";
                pretty_print_list args (fun a -> INT a) "[" "," "]"]))
    
  method index_funargs (r: bfunarg_t list) =
    let r =
      List.mapi (fun i (name, typ, attrs) ->
          let name =
            if name = "" then "$par$" ^ (string_of_int (i+1)) else name in
          (name,typ,attrs)) r in
    funargs_table#add ([], List.map self#index_funarg r)

  method get_funargs (index: int): bfunarg_t list =
    let (_,args) = funargs_table#retrieve index in
    List.map self#get_funarg args
    
  method private index_opt_funargs (f: bfunarg_t list option) =
    match f with None -> (-1) | Some r -> self#index_funargs r

  method private get_opt_funargs (index: int): bfunarg_t list option =
    if index = (-1) then None else Some (self#get_funargs index)

  method index_tname (t: tname_t) =
    let tags = [tname_mcts#ts t] in
    let key = match t with
      | SimpleName s -> (tags, [self#index_string s])
      | TemplatedName (name, tl) ->
         (tags, [self#index_tname name] @ (List.map self#index_typ tl)) in
    tname_table#add key

  method private index_tname_list (tl: tname_t list) =
    tname_list_table#add ([], List.map self#index_tname tl)

  method index_typ (typ: btype_t):int =
    (* omit entry for empty attributes *)
    let ia attrs =
      match attrs with [] -> [(-1)] | _ -> [self#index_attributes attrs ] in
    let tags = [typ_mcts#ts typ] in
    let key = match typ with
      | TVoid attrs -> (tags, ia attrs)
      | TInt (ik,attrs) -> (tags @ [ikind_mfts#ts ik], ia attrs)
      | TFloat (fk, fp, attrs) ->
         (tags @ [fkind_mfts#ts fk; frepresentation_mfts#ts fp], ia attrs)
      | TPtr (typ, attrs) -> (tags, (self#index_typ typ) :: ia attrs)
      | TRef (typ, attrs) -> (tags, (self#index_typ typ) :: ia attrs)
      | THandle (s, attrs) -> (tags, (self#index_string s) :: ia attrs)
      | TArray (typ,optexp,attrs) ->
         (tags,
          [self#index_typ typ; self#index_opt_exp optexp] @ ia attrs)
      | TFun (typ,optfunargs,varargs,attrs) ->
         (tags,
          [self#index_typ typ;
           self#index_opt_funargs optfunargs;
           (if varargs then 1 else 0)] @ ia attrs)
      | TNamed (tname, attrs) -> (tags @ [tname], ia attrs)
      | TComp (ckey, attrs) -> (tags,  (ckey) :: ia attrs)
      | TEnum (ename, attrs) -> (tags @ [ename], ia attrs)
      | TCppComp (t, tl, attrs) ->
         (tags,
          [self#index_tname t;
           self#index_tname_list tl] @ (ia attrs))
      | TCppEnum(t, tl, attrs) ->
         (tags,
          [self#index_tname t;
           self#index_tname_list tl] @ (ia attrs))
      | TClass (t, tl, attrs) ->
         (tags,
          [self#index_tname t;
           self#index_tname_list tl] @ (ia attrs))
      | TUnknown attrs -> (tags, ia attrs)
      | TVarArg attrs -> (tags, ia attrs)
      | TBuiltin_va_list attrs -> (tags, ia attrs) in
    typ_table#add key

  method get_typ (index: int) =
    let name = typ_mcts#name in
    let (tags, args) = typ_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let attrs = self#get_attributes in
    match (t 0) with
    | "tvoid" -> TVoid (attrs (a 0))
    | "tint" -> TInt (ikind_mfts#fs (t 1), attrs (a 0))
    | "tfloat" ->
       TFloat (fkind_mfts#fs (t 1), frepresentation_mfts#fs (t 2), attrs (a 0))
    | "tptr" -> TPtr (self#get_typ (a 0), attrs (a 1))
    | "tarray" ->
       TArray (self#get_typ (a 0), self#get_opt_exp (a 1), attrs (a 2))
    | "tfun" ->
       TFun (self#get_typ (a 0),
             self#get_opt_funargs (a 1),
             (a 2) = 1,
             attrs (a 3))
    | "tnamed" -> TNamed (t 1, attrs (a 0))
    | "tcomp" -> TComp (a 0, attrs (a 1))
    | "tenum" -> TEnum (t 1, attrs (a 0))
    | "tbuiltin-va-list" -> TBuiltin_va_list (attrs (a 0))
    | "tvararg" -> TVarArg (attrs (a 0))
    | "tunknown" -> TUnknown (attrs (a 0))
    | s -> raise_tag_error name s typ_mcts#tags

  method index_string (s: string) = string_table#add s

  method get_string (index:int) = string_table#retrieve index

  method index_location (l: b_location_t) =
    let key = ([], [l.line; self#index_string l.file; l.byte]) in
    location_table#add key

  method get_location (index: int): b_location_t =
    let (_, args) = location_table#retrieve index in
    let a = a "b_location_t" args in
    {line = a 0; file = self#get_string (a 1); byte = a 2}

  method private index_typsig_list (tsigs: btypsig_t list):int =
    typsiglist_table#add ([],List.map self#index_typsig tsigs)

  method private index_typsig_list_option (opttsigs: btypsig_t list option):int =
    match opttsigs with Some tsigs -> self#index_typsig_list tsigs | _ -> (-1)

  method private get_typsig_list (index:int): btypsig_t list =
    let (_,args) = typsiglist_table#retrieve index in
    List.map self#get_typsig args

  method private get_typsig_list_option (index: int): btypsig_t list option =
    if index = (-1) then None else
      Some (self#get_typsig_list index)
    
  method index_typsig (typsig: btypsig_t):int =
    let tags = [ typsig_mcts#ts typsig] in
    (* omit entry for empty attributes *)
    let ia attrs =
      match attrs with [] -> [] | _ -> [self#index_attributes attrs] in
    let key = match typsig with
      | TSArray (tsig, opti64, attrs) ->
         (tags @ [self#index_opti64 opti64],
          [self#index_typsig tsig ] @ ia attrs)
      | TSPtr (tsig, attrs) -> (tags, (self#index_typsig tsig) :: ia attrs)
      | TSComp (b,s,attrs) -> (tags @ [s],  (if b then 1 else 0) :: ia attrs)
      | TSFun (tsig,tsigs,b,attrs) ->
         (tags,
          [self#index_typsig tsig;
           self#index_typsig_list_option tsigs;
           (if b then 1 else 0) ] @ ia attrs)
      | TSEnum (name,attrs) -> (tags @ [name], ia attrs)
      | TSBase typ -> (tags, [self#index_typ typ ]) in
    typsig_table#add key

  method get_typsig (index: int): btypsig_t =
    let name = "typsig" in
    let (tags, args) = typsig_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let attrs n =
      if List.length args > n then self#get_attributes (a n) else [] in
    match (t 0) with
    | "tsarray" -> 
       TSArray (self#get_typsig (a 0), self#get_opti64 (t 1), attrs 1)
    | "tsptr" -> TSPtr (self#get_typsig (a 0), attrs 1)
    | "tscomp" -> TSComp ((a 0) = 1, (t 1), attrs 1)
    | "tsfun" ->
       TSFun
         (self#get_typsig (a 0),
          self#get_typsig_list_option (a 1), (a 2) = 1,
          attrs 3)
    | "tsenum" -> TSEnum (t 1, attrs 0)
    | "tsbase" -> TSBase (self#get_typ (a 0))
    | s -> raise_tag_error name s typsig_mcts#tags

  method index_init_opt (iinfo: binit_t option) =
    match  iinfo with
    | None -> (-1)
    | Some init -> self#index_init init

  method index_init (init: binit_t) =
    let (tags, args) = match init with
      | SingleInit exp -> (["single"], [self#index_exp exp])
      | CompoundInit (typ,olist) when (List.length olist) > 5000 ->
         (["compound"],
          [(self#index_typ typ); self#index_offset_init (List.hd olist)])
      | CompoundInit (typ, olist) ->
         (["compound"],
          (self#index_typ typ) :: (List.map self#index_offset_init olist)) in
    initinfo_table#add (tags, args)

  method get_init (index: int): binit_t =
    let name = "binit_t" in
    let (tags, args) = initinfo_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "single" -> SingleInit (self#get_exp (a 0))
    | "compound" ->
       CompoundInit
         (self#get_typ (a 0), List.map self#get_offset_init (List.tl args))
    | s -> raise_tag_error name s ["single"; "compound"]
                                        
  method index_offset_init (oi: (boffset_t * binit_t)) =
    let (offset, init) = oi in
    let args = [self#index_offset offset; self#index_init init] in
    offset_init_table#add ([], args)

  method get_offset_init (index: int): (boffset_t * binit_t) =
    let (_, args) = offset_init_table#retrieve index in
    let a = a "offset_init" args in
    (self#get_offset (a 0), self#get_init (a 1))
    
  method index_varinfo (vinfo: bvarinfo_t) =
    let vinit_ix = match vinfo.bvinit with
      | Some i -> self#index_init i
      | _ -> (-1) in
    let tags = [vinfo.bvname; storage_mfts#ts vinfo.bvstorage] in
    let args = [
        vinfo.bvid;
        self#index_typ vinfo.bvtype;
        self#index_attributes vinfo.bvattr;
        ibool vinfo.bvglob;
        ibool vinfo.bvinline;
        self#index_location vinfo.bvdecl;
        ibool vinfo.bvaddrof;
        0;
        vinit_ix] in
    varinfo_table#add (tags, args)

  method get_varinfo (index: int): bvarinfo_t =
    let name = "bvarinfo_t" in
    let (tags, args) = varinfo_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    {
      bvname = (t 0);
      bvstorage = storage_mfts#fs (t 1);
      bvid = (a 0);
      bvtype = self#get_typ (a 1);
      bvattr = self#get_attributes (a 2);
      bvglob = (a 3) = 1;
      bvinline = (a 4) = 1;
      bvdecl = self#get_location (a 5);
      bvaddrof = (a 6) = 1;
      bvparam = (a 7);
      bvinit = if (a 8) = -1 then None else Some (self#get_init (a 8))
    }

  method index_fieldinfo (finfo: bfieldinfo_t) =
    let tags = [finfo.bfname] in
    let args =
      [finfo.bfckey;
       self#index_typ finfo.bftype;
       (match finfo.bfbitfield with Some b -> b | _ -> -1);
       self#index_attributes finfo.bfattr;
       self#index_location finfo.bfloc]
      @ (match finfo.bfieldlayout with
         | Some (offset, size) -> [offset; size]
         | _ -> []) in
    fieldinfo_table#add (tags,args)

  method get_fieldinfo (index: int): bfieldinfo_t =
    let (tags, args) = fieldinfo_table#retrieve index in
    let t = t "bfieldinfo_t" tags in
    let a = a "bfieldinfo_t" args in
    {
      bfname = t 0;
      bfckey = a 0;
      bftype = self#get_typ (a 1);
      bfbitfield = if (a 2) = (-1) then None else Some (a 2);
      bfattr = self#get_attributes (a 3);
      bfloc = self#get_location (a 4);
      bfieldlayout =
        if (List.length args) = 7 then
          Some ((a 5), (a 6))
        else
          None
    }

  method index_compinfo (cinfo: bcompinfo_t) =
    let tags = [cinfo.bcname] in
    let args =
      [cinfo.bckey;
       ibool cinfo.bcstruct;
       self#index_attributes cinfo.bcattr]
      @ (List.map self#index_fieldinfo cinfo.bcfields) in
    compinfo_table#add (tags, args)

  method get_compinfo (index: int): bcompinfo_t =
    let (tags, args) = compinfo_table#retrieve index in
    let t = t "bcompinfo_t" tags in
    let a = a "bcompinfo_t" args in
    { bcname = t 0;
      bckey = a 0;
      bcstruct = (a 1) = 1;
      bcattr = self#get_attributes (a 2);
      bcfields = List.map self#get_fieldinfo (get_list_suffix args 3)
    }

  method index_enumitem (eitem: beitem_t) =
    let (name, exp, loc) = eitem in
    let tags = [name] in
    let args = [self#index_exp exp; self#index_location loc] in
    enumitem_table#add (tags, args)

  method get_enumitem (index: int): beitem_t =
    let (tags, args) = enumitem_table#retrieve index in
    let t = t "beitem_t" tags in
    let a = a "beitem_t" args in
    (t 0, self#get_exp (a 0), self#get_location (a 1))

  method index_enuminfo (einfo: benuminfo_t) =
    let tags = [einfo.bename; ikind_mfts#ts einfo.bekind] in
    let args =
      [self#index_attributes einfo.beattr]
      @ (List.map self#index_enumitem einfo.beitems) in
    enuminfo_table#add (tags, args)

  method get_enuminfo (index: int): benuminfo_t =
    let (tags, args) = enuminfo_table#retrieve index in
    let t = t "benuminfo_t" tags in
    let a = a "benuminfo_t" args in
    let attrs = self#get_attributes in
    { bename = (t 0);
      bekind = ikind_mfts#fs (t 1);
      beitems = List.map self#get_enumitem (List.tl args);
      beattr = attrs (a 0)
    }

  method index_typeinfo (tinfo: btypeinfo_t) =
    let tags = [tinfo.btname] in
    let args = [self#index_typ tinfo.bttype] in
    typeinfo_table#add (tags, args)

  method get_typeinfo (index: int): btypeinfo_t =
    let name = "btypeinfo_t" in
    let (tags, args) = typeinfo_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    {
      btname = t 0;
      bttype = self#get_typ (a 0)
    }
    
  method write_xml_attributes
           ?(tag="iattrs") (node: xml_element_int) (attr: b_attributes_t) =
    node#setIntAttribute tag (self#index_attributes attr)

  method read_xml_attributes
           ?(tag="iattrs") (node: xml_element_int): b_attributes_t =
    self#get_attributes (node#getIntAttribute tag)
       
  method write_xml_exp ?(tag="iexp") (node:xml_element_int) (exp: bexp_t) =
    node#setIntAttribute tag (self#index_exp exp)

  method read_xml_exp ?(tag="iexp") (node: xml_element_int): bexp_t =
    self#get_exp (node#getIntAttribute tag)

  method write_xml_funarg_list
           ?(tag="ifunargs") (node: xml_element_int) (r: bfunarg_t list) =
    node#setIntAttribute tag (self#index_funargs r)

  method read_xml_funarg_list
           ?(tag="ifunargs") (node: xml_element_int): bfunarg_t list =
    self#get_funargs (node#getIntAttribute tag)
    
  method write_xml_lval ?(tag="ilval") (node:xml_element_int) (lval: blval_t) =
    node#setIntAttribute tag (self#index_lval lval)

  method read_xml_lval ?(tag="ilval") (node: xml_element_int): blval_t =
    self#get_lval (node#getIntAttribute tag)

  method write_xml_offset
           ?(tag="ioffset") (node: xml_element_int) (offset: boffset_t) =
    node#setIntAttribute tag (self#index_offset offset)

  method read_xml_offset
           ?(tag="ioffset") (node: xml_element_int): boffset_t =
    self#get_offset (node#getIntAttribute tag)

  method write_xml_typ ?(tag="ityp") (node:xml_element_int) (typ: btype_t) =
    node#setIntAttribute tag (self#index_typ typ)

  method read_xml_typ ?(tag="ityp") (node: xml_element_int): btype_t =
    self#get_typ (node#getIntAttribute tag)

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s: string) =
    node#setIntAttribute tag (self#index_string s)

  method write_xml_varinfo
           ?(tag="ivinfo") (node: xml_element_int) (vinfo: bvarinfo_t) =
    node#setIntAttribute tag (self#index_varinfo vinfo)

  method read_xml_varinfo
           ?(tag="ivinfo") (node: xml_element_int): bvarinfo_t =
    self#get_varinfo (node#getIntAttribute tag)

  method write_xml_init ?(tag="iinit") (node:xml_element_int) (init: binit_t) =
    node#setIntAttribute tag (self#index_init init)

  method read_xml_init ?(tag="iinit") (node: xml_element_int): binit_t =
    self#get_init (node#getIntAttribute tag)

  method write_xml_fieldinfo
           ?(tag="ifinfo") (node: xml_element_int) (finfo: bfieldinfo_t) =
    node#setIntAttribute tag (self#index_fieldinfo finfo)

  method read_xml_fieldinfo
           ?(tag="ifinfo") (node: xml_element_int): bfieldinfo_t =
    self#get_fieldinfo (node#getIntAttribute tag)

  method write_xml_compinfo
           ?(tag="icinfo") (node: xml_element_int) (cinfo: bcompinfo_t) =
    node#setIntAttribute tag (self#index_compinfo cinfo)

  method read_xml_compinfo
           ?(tag="icinfo") (node: xml_element_int): bcompinfo_t =
    self#get_compinfo (node#getIntAttribute tag)

  method write_xml_enumitem
           ?(tag="ieitem") (node: xml_element_int) (eitem: beitem_t) =
    node#setIntAttribute tag (self#index_enumitem eitem)

  method write_xml_enuminfo
           ?(tag="ieinfo") (node:xml_element_int) (einfo: benuminfo_t) =
    node#setIntAttribute tag (self#index_enuminfo einfo)

  method read_xml_enuminfo
           ?(tag="ieinfo") (node: xml_element_int): benuminfo_t =
    self#get_enuminfo (node#getIntAttribute tag)

  method write_xml_typeinfo
           ?(tag="itinfo") (node: xml_element_int) (tinfo: btypeinfo_t) =
    node#setIntAttribute tag (self#index_typeinfo tinfo)

  method read_xml_typeinfo
           ?(tag="itinfo") (node: xml_element_int): btypeinfo_t =
    self#get_typeinfo (node#getIntAttribute tag)

  method write_xml_location
           ?(tag="iloc") (node: xml_element_int) (loc: b_location_t) =
    node#setIntAttribute tag (self#index_location loc)

  method read_xml_location
           ?(tag="iloc") (node: xml_element_int): b_location_t =
    self#get_location (node#getIntAttribute tag)
    
  method write_xml (node: xml_element_int) =
    let snode = xmlElement string_table#get_name in
    begin
      string_table#write_xml snode;
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end)
           tables);
      node#appendChildren [snode]
    end

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables;
      string_table#read_xml (getc string_table#get_name)
    end

end


let bcdictionary = new bcdictionary_t

(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHLogger
open CHIndexTable
open CHStringIndexTable
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHUtilities
open CCHSumTypeSerializer

module H = Hashtbl


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
    raise (CCHFailure msg)
  end

let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s,false, String.length s)


class cdictionary_t:cdictionary_int =
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
      typsiglist_table
   ]

  method reset =
    begin
      string_table#reset;
      List.iter (fun t -> t#reset) tables
    end

  method index_attrparam (a:attrparam) =
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
         (tags @ [unop_mfts#ts unop], [self#index_attrparam a])
      | ABinOp (binop,a1,a2) ->
         (tags @ [binop_mfts#ts binop] ,
          [self#index_attrparam a1; self#index_attrparam a2])
      | ADot (a,s) -> (tags @ [s], [self#index_attrparam a])
      | AStar a -> (tags, [self#index_attrparam a])
      | AAddrOf a -> (tags, [self#index_attrparam a])
      | AAssign (a1, a2) ->
         (tags, [self#index_attrparam a1; self#index_attrparam a2])
      | AIndex (a1,a2) ->
         (tags, [self#index_attrparam a1; self#index_attrparam a2])
      | AQuestion (a1, a2, a3) ->
         (tags,
          [self#index_attrparam a1; self#index_attrparam a2;
            self#index_attrparam a3]) in
    attrparam_table#add key

  method get_attrparam (index:int):attrparam =
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
       ABinOp (binop_mfts#fs (t 1),
               self#get_attrparam (a 0), self#get_attrparam (a 1))
    | "adot" -> ADot (self#get_attrparam (a 0), (t 1))
    | "astar" -> AStar (self#get_attrparam (a 0))
    | "aaddrof" -> AAddrOf (self#get_attrparam (a 0))
    | "aassign" -> AAssign (self#get_attrparam (a 0), self#get_attrparam (a 1))
    | "aindex" -> AIndex (self#get_attrparam (a 0), self#get_attrparam (a 1))
    | "aquestion" ->
       AQuestion (self#get_attrparam (a 0), self#get_attrparam (a 1),
                  self#get_attrparam (a 2))
    | s -> raise_tag_error name s attrparam_mcts#tags

  method index_constant (c:constant):int =
    let tags = [constant_mcts#ts c] in
    let key = match c with
      | CInt (i64,ik, _opts) ->
         (tags @ [Int64.to_string i64; ikind_mfts#ts ik], [])
      | CStr s -> (tags, [self#index_string s])
      | CWStr i64r -> (tags @ (List.map Int64.to_string i64r), [])
      | CChr c -> (tags, [Char.code c])
      | CReal (f,fk,opts) ->
         (tags @ [string_of_float f; fkind_mfts#ts fk;
                   match opts with Some s -> s | _ -> ""], [])
      | CEnum (exp,ename,iname) ->
         (tags @ [ename; iname], [self#index_exp exp]) in
    constant_table#add key

  method get_constant (index:int):constant =
    let name = "constant" in
    let (tags,args) = constant_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "int" ->
       CInt (Int64.of_string (t 1), ikind_mfts#fs (t 2),None)
    | "str" -> CStr (self#get_string (a 0))
    | "wstr" -> CWStr (List.map Int64.of_string (List.tl tags))
    | "chr" -> CChr (Char.chr (a 0))
    | "real" ->
       let t3 = if (List.length tags) > 3 then (t 3) else "" in
       CReal (float_of_string (t 1), fkind_mfts#fs (t 2),
              let s = t3 in if s = "" then None else Some s)
    | "enum" -> CEnum (self#get_exp (a 0), t 1, t 2)
    | s -> raise_tag_error name s constant_mcts#tags

  method index_lval ((lhost, offset):lval):int =
    lval_table#add ([], [self#index_lhost lhost; self#index_offset offset])

  method get_lval (index:int):lval =
    let (_,args) = lval_table#retrieve index in
    match args with
    | [lhostindex; offsetindex] ->
       (self#get_lhost lhostindex, self#get_offset offsetindex)
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "lval invalid format: ";
                 pretty_print_list args (fun i -> INT i) "[" ";" "]"]))

  method index_lhost (h:lhost):int =
    let key = match h with
    | Var (vname,vid) -> (["var"; vname], [vid])
    | Mem exp -> (["mem"], [self#index_exp exp]) in
    lhost_table#add key

  method get_lhost (index:int):lhost =
    let name = "lhost" in
    let (tags,args) = lhost_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "var" -> Var (t 1, a 0)
    | "mem" -> Mem (self#get_exp (a 0))
    | s -> raise_tag_error name s ["var"; "mem"]

  method index_offset (offset:offset):int =
    let tags = [offset_mcts#ts offset] in
    let key = match offset with
      | NoOffset -> (tags, [])
      | Field ((fname,fkey), suboffset ) ->
         (tags @ [fname], [fkey; self#index_offset suboffset])
      | Index (exp,suboffset) ->
         (tags, [self#index_exp exp; self#index_offset suboffset]) in
    offset_table#add key

  method get_offset (index:int):offset =
    let name = "offset" in
    let (tags,args) = offset_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "n" -> NoOffset
    | "f" -> Field ((t 1, a 0), self#get_offset (a 1))
    | "i" -> Index (self#get_exp (a 0), self#get_offset (a 1))
    | s -> raise_tag_error name s offset_mcts#tags

  method index_opt_lval (l:lval option) =
    match l with Some lval -> self#index_lval lval | _ -> (-1)

  method get_opt_lval (index:int) =
    if index = -1 then None else Some (self#get_lval index)

  method private index_opt_exp (x:exp option) =
    match x with Some e -> self#index_exp e | _ -> (-1)

  method private get_opt_exp (index:int) =
    if index = -1 then None else Some (self#get_exp index)

  method private index_opt_exp_list (r:exp option list) =
    List.map self#index_opt_exp r

  method private get_opt_exp_list (r:int list) =
    List.map self#get_opt_exp r

  method index_exp (exp:exp) =
    let tags = [exp_mcts#ts exp] in
    let key = match exp with
    | Const c -> (tags,[self#index_constant c])
    | Lval lval -> (tags,[self#index_lval lval])
    | SizeOf typ -> (tags,[self#index_typ typ])
    | SizeOfE exp -> (tags,[self#index_exp exp])
    | SizeOfStr s -> (tags, [self#index_string s])
    | AlignOf typ -> (tags, [self#index_typ typ])
    | AlignOfE exp -> (tags, [self#index_exp exp])
    | UnOp (unop,exp,typ) ->
       (tags @ [unop_mfts#ts unop],
        [self#index_exp exp; self#index_typ typ])
    | BinOp (binop,exp1,exp2,typ) ->
       (tags @ [binop_mfts#ts binop],
        [self#index_exp exp1; self#index_exp exp2; self#index_typ typ])
    | Question (exp1,exp2,exp3,typ) ->
       (tags,
        [self#index_exp exp1; self#index_exp exp2; self#index_exp exp3;
         self#index_typ typ])
    | CastE (typ,exp) ->
       (tags, [self#index_typ typ; self#index_exp exp])
    | AddrOf lval -> (tags, [self#index_lval lval])
    | AddrOfLabel label -> (tags, [label])
    | StartOf lval -> (tags, [self#index_lval lval])
    | FnApp (loc,exp,optexps) ->
       (tags @ [loc.file],
        [loc.line; loc.byte;
         self#index_exp exp] @ (self#index_opt_exp_list optexps))
    | CnApp (name,optexps,typ) ->
       (tags @ [name],
        (self#index_typ typ) :: (self#index_opt_exp_list optexps)) in
    exp_table#add key

  method get_exp (index:int):exp =
    try
      let name = "exp" in
      let (tags,args) = exp_table#retrieve index in
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
         Question (self#get_exp (a 0), self#get_exp (a 1), self#get_exp (a 2),
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
    with
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Failure in cdictionary get_exp ";
                 INT index;
                 STR ": ";
                 STR s]))

  method private index_attribute (a:attribute) =
    match a with
    | Attr (name, attrparams) ->
       attribute_table#add ([name], List.map self#index_attrparam attrparams)

  method private get_attribute (index:int):attribute =
    let (tags,args) = attribute_table#retrieve index in
    if (List.length tags) > 0 then
      Attr (List.hd tags, List.map self#get_attrparam args)
    else
      raise (CCHFailure (LBLOCK [STR "Attribute without a name "]))

  method private index_attributes (r:attributes) =
    attributes_table#add ([], List.map self#index_attribute r)

  method private get_attributes (index:int):attributes =
    if index = (-1) then [] else
    let (_,args) = attributes_table#retrieve index in
    List.map self#get_attribute args

  method private index_funarg ((name,typ,attrs):funarg) =
    funarg_table#add ( [name], [self#index_typ typ; self#index_attributes attrs])

  method private get_funarg (index:int):funarg =
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
        (CCHFailure
           (LBLOCK [
                STR "Invalid funarg: ";
                STR "tags: ";
                pretty_print_list tags (fun s -> STR s) "[" "," "], ";
                STR "args: ";
                pretty_print_list args (fun a -> INT a) "[" "," "]"]))

  method index_funargs (r:funarg list) =
    let r =
      List.mapi (fun i (name,typ,attrs) ->
          let name =
            if name = "" then "$par$" ^ (string_of_int (i+1)) else name in
          (name,typ,attrs)) r in
    funargs_table#add ([], List.map self#index_funarg r)

  method get_funargs (index:int):funarg list =
    let (_,args) = funargs_table#retrieve index in
    List.map self#get_funarg args

  method private index_opt_funargs (f:funarg list option) =
    match f with None -> (-1) | Some r -> self#index_funargs r

  method private get_opt_funargs (index:int):funarg list option =
    if index = (-1) then None else Some (self#get_funargs index)

  method index_typ (typ:typ):int =
    let tags = [typ_mcts#ts typ] in
    let ia attrs =
      match attrs with [] -> [] | _ -> [self#index_attributes attrs] in
    let key = match typ with
      | TVoid attrs -> (tags, ia attrs )
      | TInt (ik,attrs) -> (tags @ [ikind_mfts#ts ik], ia attrs)
      | TFloat (fk,attrs) -> (tags @ [fkind_mfts#ts fk], ia attrs)
      | TPtr (typ,attrs) -> (tags, (self#index_typ typ) :: ia attrs)
      | TArray (typ,optexp,attrs) ->
         (tags,
          [self#index_typ typ; self#index_opt_exp optexp] @ ia attrs)
      | TFun (typ,optfunargs,varargs,attrs) ->
         (tags, [self#index_typ typ; self#index_opt_funargs optfunargs;
                      (if varargs then 1 else 0)] @ ia attrs)
      | TNamed (name,attrs) -> (tags @ [name], ia attrs)
      | TComp (key, attrs) -> (tags, key :: ia attrs )
      | TEnum (name, attrs) -> (tags @ [name], ia attrs)
      | TBuiltin_va_list attrs -> (tags, ia attrs) in
    typ_table#add key

  method get_typ (index:int):typ =
    try
      let name = "typ" in
      let (tags,args) = typ_table#retrieve index in
      let a = a name args in
      let t = t name tags in
      let attrs n =
        if List.length args > n then self#get_attributes (a n) else [] in
      match (t 0) with
      | "tvoid" -> TVoid (attrs 0)
      | "tint" -> TInt (ikind_mfts#fs (t 1), attrs 0)
      | "tfloat" -> TFloat (fkind_mfts#fs (t 1), attrs 0)
      | "tptr" -> TPtr (self#get_typ (a 0), attrs 1)
      | "tarray" ->
         TArray (self#get_typ (a 0), self#get_opt_exp (a 1), attrs 2)
      | "tfun" ->
         TFun (self#get_typ (a 0), self#get_opt_funargs (a 1),
               (a 2) =  1, attrs 3)
      | "tnamed" -> TNamed (t 1, attrs 0)
      | "tcomp" -> TComp (a 0, attrs 1)
      | "tenum" -> TEnum (t 1, attrs 0)
      | "tbuiltin-va-list" -> TBuiltin_va_list (attrs 0)
      | s -> raise_tag_error name s typ_mcts#tags
    with
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Failure in cdictionary get_typ ";
                 INT index;
                 STR ": ";
                 STR s]))

  method private index_opti64(i64:int64 option):string =
    match i64 with Some i -> Int64.to_string i | _ -> ""

  method private get_opti64 (s:string):int64 option =
    match s with "" -> None | _ -> Some (Int64.of_string s)

  method private index_typsig_list (tsigs:typsig list):int =
    typsiglist_table#add ([],List.map self#index_typsig tsigs)

  method private index_typsig_list_option (opttsigs:typsig list option):int =
    match opttsigs with Some tsigs -> self#index_typsig_list tsigs | _ -> (-1)

  method private get_typsig_list (index:int):typsig list =
    let (_,args) = typsiglist_table#retrieve index in
    List.map self#get_typsig args

  method private get_typsig_list_option (index:int):typsig list option =
    if index = (-1) then None else
      Some (self#get_typsig_list index)


  method index_typsig (typsig:typsig):int =
    let tags = [typsig_mcts#ts typsig] in
    let ia attrs =
      match attrs with [] -> [] | _ -> [self#index_attributes attrs] in
    let key = match typsig with
      | TSArray (tsig, opti64, attrs) ->
         (tags @ [self#index_opti64 opti64],
          (self#index_typsig tsig) :: ia attrs)
      | TSPtr (tsig, attrs) ->
         (tags,(self#index_typsig tsig) :: ia attrs)
      | TSComp (b,s,attrs) ->
         (tags @ [s],(if b then 1 else 0) :: ia attrs)
      | TSFun (tsig,tsigs,b,attrs) ->
         (tags,[self#index_typsig tsig; self#index_typsig_list_option tsigs;
                      (if b then 1 else 0)] @ ia attrs )
      | TSEnum (name,attrs) -> (tags @ [name], ia attrs)
      | TSBase typ -> (tags, [self#index_typ typ]) in
    typsig_table#add key

  method get_typsig (index:int):typsig =
    let name = "typsig" in
    let (tags,args) = typsig_table#retrieve index in
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
       TSFun (
           self#get_typsig (a 0),
           self#get_typsig_list_option (a 1),
           (a 2) = 1,
           attrs 3)
    | "tsenum" -> TSEnum (t 1, attrs 0)
    | "tsbase" -> TSBase (self#get_typ (a 0))
    | s -> raise_tag_error name s typsig_mcts#tags

  method index_string (s:string):int = string_table#add s

  method get_string (index:int) = string_table#retrieve index

  method read_xml_attributes ?(tag="iattrs") (node:xml_element_int):attributes =
    if node#hasNamedAttribute tag then
      self#get_attributes (node#getIntAttribute tag)
    else
      []

  method write_xml_exp ?(tag="iexp") (node:xml_element_int) (exp:exp) =
    node#setIntAttribute tag (self#index_exp exp)

  method write_xml_exp_opt
           ?(tag="iexp") (node:xml_element_int) (optexp:exp option) =
    match optexp with
    | Some exp -> self#write_xml_exp ~tag node exp
    | _ -> ()

  method read_xml_exp ?(tag="iexp") (node:xml_element_int):exp =
    try
      self#get_exp (node#getIntAttribute tag)
    with
    | Failure s ->
       raise (CCHFailure (LBLOCK [STR "Failure in read_xml_exp: "; STR s]))

  method read_xml_exp_opt ?(tag="iexp") (node:xml_element_int):exp option =
    if node#hasNamedAttribute tag then
      Some (self#read_xml_exp ~tag node)
    else
      None

  method read_xml_funarg_list
           ?(tag="ifunargs") (node:xml_element_int):funarg list =
    self#get_funargs (node#getIntAttribute tag)

  method write_xml_lval ?(tag="ilval") (node:xml_element_int) (lval:lval) =
    node#setIntAttribute tag (self#index_lval lval)

  method read_xml_lval ?(tag="ilval") (node:xml_element_int):lval =
    self#get_lval (node#getIntAttribute tag)

  method read_xml_lval_opt ?(tag="ilval") (node:xml_element_int):lval option =
    if node#hasNamedAttribute tag then
      Some (self#read_xml_lval ~tag node)
    else
      None

  method write_xml_offset ?(tag="ioffset") (node:xml_element_int) (offset:offset) =
    node#setIntAttribute tag (self#index_offset offset)

  method read_xml_offset ?(tag="ioffset") (node:xml_element_int):offset =
    if node#hasNamedAttribute tag then
      self#get_offset (node#getIntAttribute tag)
    else
      NoOffset

  method write_xml_typ ?(tag="ityp") (node:xml_element_int) (typ:typ) =
    node#setIntAttribute tag (self#index_typ typ)

  method read_xml_typ ?(tag="ityp") (node:xml_element_int):typ =
    self#get_typ (node#getIntAttribute tag)

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    let snode = xmlElement string_table#get_name in
    begin
      string_table#write_xml snode;
      node#appendChildren [snode];
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      string_table#read_xml (getc string_table#get_name);
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

  method toPretty =
    LBLOCK [
        STR "string-table: ";
        INT string_table#size;
        NL;
        (LBLOCK
           (List.map (fun t ->
                LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables))]

end


let cdictionary = new cdictionary_t

(* =============================================================================
   CodeHawk Binary Analyzer
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
open CHNumerical
open CHPretty

(* chutil *)
open CHUtil

(* bchlib *)
open BCHBCTypes


let string_printer = CHPrettyUtil.string_printer
let p2s = string_printer#print


let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s, false, String.length s)


let location_line_to_string (loc: b_location_t) =
  loc.file ^ "@" ^ (string_of_int loc.line)


let storage_to_string (s: bstorage_t) =
  match s with
  | NoStorage -> ""
  | Static -> "static"
  | Register -> "register"
  | Extern -> "extern"
  | Opaque i -> "opaque_" ^  (string_of_int i)


let location_to_pretty (loc: b_location_t) =
  LBLOCK [
      STR loc.file;
      STR " @ ";
      INT loc.line;
      STR " (";
      INT loc.byte;
      STR ")"]


let int_type_to_string (k: ikind_t) =
  match k with
  | IChar -> "char"
  | ISChar -> "signed char"
  | IUChar -> "unsigned char"
  | IWChar -> "wchar_t"
  | IBool -> "bool"
  | IInt -> "int"
  | IUInt -> "unsigned int"
  | IShort -> "short"
  | IUShort -> "unsigned short"
  | ILong -> "long"
  | IULong -> "unsigned long"
  | ILongLong -> "long long"
  | IULongLong -> "unsigned long long"
  | IInt128 -> "int128_t"
  | IUInt128 -> "uint128_t"
  | INonStandard (issigned, size) ->
     let prefix = if issigned then "int" else "uint" in
     prefix ^ (string_of_int (size / 4)) ^ "_t"


let unop_to_print_string (op: unop_t) =
  match op with
  | Neg -> " - "
  | BNot -> " ~ "
  | LNot -> " ! "


let binop_to_print_string (op: binop_t) =
  match op with
  | PlusA -> " + "
  | PlusPI -> " +i "
  | IndexPI -> " +i "
  | MinusA -> " - "
  | MinusPI -> " -i "
  | MinusPP -> " -p "
  | Mult -> " * "
  | Div -> " / "
  | Mod -> " % "
  | Shiftlt -> " << "
  | Shiftrt -> " >> "
  | Lt -> " < "
  | Gt -> " > "
  | Le -> " <= "
  | Ge -> " >= "
  | Eq -> " == "
  | Ne -> " != "
  | BAnd -> " & "
  | BXor -> " ^ "
  | BOr -> " | "
  | LAnd -> " && "
  | LOr -> " || "


let float_representation_to_string (r: frepresentation_t) =
  match r with
  | FScalar -> "scalar"
  | FPacked -> "packed"


let float_type_to_string (k: fkind_t) =
  match k with
  | FFloat -> "float"
  | FDouble -> "double"
  | FLongDouble -> "long double"
  | FComplexFloat -> "complex"
  | FComplexDouble -> "double complex"
  | FComplexLongDouble -> "long double complex"


let cil_constant_to_string (c: bconstant_t) =
  match c with
  | CInt (_,_,Some t) -> t
  | CInt (i64,_,_) -> Int64.to_string i64
  | CStr s ->
     let (_,_,len) = mk_constantstring s in
     (string_of_int len) ^ "-char-string-literal"
  | CWStr l64 -> String.concat " " (List.map Int64.to_string l64)
  | CChr c -> string_of_int (Char.code c)
  | CReal (_,_,Some t) -> t
  | CReal (f,_,_)  -> string_of_float f
  | CEnum (_,s,_) -> s


let constant_to_string (c: bconstant_t) =
  match c with
  | CStr s ->
     let (_,_,len) = mk_constantstring s in
     (string_of_int len) ^ "-char-string"
  | _ -> cil_constant_to_string c


let attributes_to_string attrs =
  match attrs with
  | [] -> ""
  | l ->
     (String.concat
        "," (List.map (fun attr -> match attr with Attr (s, _) -> s) l)) ^ " "


let rec typ_to_string (t: btype_t) =
  let ns_to_string ns =
    String.concat "" (List.map (fun n -> (tname_to_string n) ^ "::") ns) in
  let a = attributes_to_string in
  match t with
  | TVoid attrs -> (a attrs) ^ "void"
  | TInt (ikind, attrs) -> (a attrs) ^ int_type_to_string ikind
  | TFloat (fkind, _, attrs) -> (a attrs) ^ float_type_to_string fkind
  | TPtr (tt, attrs) -> (a attrs) ^ "(" ^ (typ_to_string tt) ^ "*)"
  | TRef (tt, attrs) -> (a attrs) ^ "(" ^ (typ_to_string tt) ^ "*)"
  | THandle (n, attrs) -> (a attrs) ^ "H" ^ n
  | TArray (tt,Some x, attrs) ->
     (a attrs) ^ (typ_to_string tt) ^ "[" ^ (p2s (exp_to_pretty x)) ^ "]"
  | TArray (tt, None, attrs) -> (a attrs) ^ (typ_to_string tt) ^ "[]"
  | TFun (tt, optArgs, _vararg, attrs) ->
     (a attrs)
     ^ "("
     ^ (typ_to_string tt)
     ^ " ("
     ^ (String.concat
          ","
          (match optArgs with
           | None -> []
           | Some args ->
              (List.map
                 (fun (name, ty, _) -> name ^ ":" ^ (typ_to_string ty)) args)))
     ^ ") )"
  | TNamed (name, attrs) -> (a attrs) ^ name
  | TComp (key, attrs) -> (a attrs) ^ "struct " ^ (string_of_int key)
  | TEnum (name, attrs) -> (a attrs) ^ "enum " ^ name
  | TCppComp (tn, ns, attrs) ->
     (a attrs) ^ "cpp struct " ^ (ns_to_string ns) ^ (tname_to_string tn)
  | TCppEnum (tn, ns, attrs) ->
     (a attrs) ^ "cpp enum " ^ (ns_to_string ns) ^ (tname_to_string tn)
  | TClass (tn, ns, attrs) ->
     (a attrs) ^ "class " ^ (ns_to_string ns) ^ (tname_to_string tn)
  | TVarArg attrs -> (a attrs) ^ "vararg"
  | TBuiltin_va_list attrs -> (a attrs) ^ "builtin_va_list"
  | TUnknown _ -> "unknown"


and tname_to_string t =
  match t with
  | SimpleName s -> s
  | TemplatedName (base,args) ->
     (tname_to_string base)
     ^ "<"
     ^ (String.concat "," (List.map typ_to_string args))
     ^ ">"


and typ_to_pretty (t: btype_t) = STR (typ_to_string t)


and cil_exp_to_pretty (x: bexp_t) =
  let pe = cil_exp_to_pretty in
  let pl = cil_lval_to_pretty in
  let peo = opt_cil_exp_to_pretty in
  match x with
  | Const c -> STR (cil_constant_to_string c)
  | Lval l -> LBLOCK [STR "lval ("; pl l ; STR ")"]
  | SizeOf t -> LBLOCK [STR "sizeof ("; typ_to_pretty t; STR ")"]
  | Real e -> LBLOCK [STR "real ("; pe e; STR ")"]
  | Imag e -> LBLOCK [STR "imag ("; pe e; STR ")"]
  | SizeOfE e -> LBLOCK [STR "sizeofe ("; pe e; STR ")"]
  | SizeOfStr s ->
     let (_,_,len) = mk_constantstring s in
     LBLOCK [STR "sizeofstr ("; INT len; STR "-char-string)"]
  | AlignOf t -> LBLOCK [STR "alignof (";  typ_to_pretty t; STR ")"]
  | AlignOfE e -> LBLOCK [STR "alignofe ("; pe e ; STR ")" ]
  | UnOp (op,e,t) ->
     LBLOCK [
         STR "((";
         STR (unop_to_print_string op);
         STR " ";
         pe e;
	 STR "):";
         typ_to_pretty t;
         STR ")"]
  | BinOp (op,e1,e2,t) ->
     LBLOCK [
         STR "((";
         pe e1;
         STR (binop_to_print_string op);
         pe e2;
	 STR "):";
         typ_to_pretty t]
  | Question (e1,e2,e3,t) ->
     LBLOCK [
         STR "((";
         pe e1;
         STR " ? ";
         pe e2;
         STR " : ";
	 pe e3;
         STR "):";
         typ_to_pretty t;
         STR ")"]
  | CastE (t,e) ->
     LBLOCK [STR "caste ("; pe e; STR ":"; typ_to_pretty t; STR ")"]
  | AddrOf l -> LBLOCK [STR "addrof ("; pl l; STR ")"]
  | AddrOfLabel l -> LBLOCK [STR "addroflabel ("; INT l; STR ")"]
  | StartOf l -> LBLOCK [STR "startof ("; pl l; STR ")"]
  | FnApp (loc,e,el) ->
     LBLOCK [
         STR "fn(";
         pe e;
         STR ")@ ";
         INT loc.line;
	 pretty_print_list el peo "[" ", " "]"]
  | CnApp (s, el, _t) ->
    begin
      match el with
      | [] -> STR s
      | _ -> LBLOCK [STR s; pretty_print_list el peo "[" ", " "]"]
    end


and opt_cil_exp_to_pretty (e: bexp_t option) =
  match e with Some e -> exp_to_pretty e | _ -> STR "_"


and exp_to_pretty (x: bexp_t) =
  let pe = exp_to_pretty in
  let pl = lval_to_pretty in
  let peo = opt_exp_to_pretty in
  match x with
  | CastE (_, CastE (TPtr (TVoid _,_),Const (CInt (i64,_,_))))
       when (mkNumericalFromInt64 i64)#equal numerical_zero -> STR "NULL"
  | Const c -> STR (constant_to_string c)
  | Lval l -> pl l
  | SizeOfE e -> LBLOCK [STR "sizeof("; pe e; STR ")"]
  | AlignOfE e -> LBLOCK [STR "alignof("; pe e; STR ")"]
  | UnOp (op,e,t) ->
     LBLOCK [
         STR "((";
         STR (unop_to_print_string op);
         STR " ";
         pe e;
	 STR "):";
         typ_to_pretty t;
         STR ")"]
  | BinOp (op,e1,e2,t) ->
     LBLOCK [
         STR "((";
         pe e1;
         STR (binop_to_print_string op);
         pe e2;
	 STR "):";
         typ_to_pretty t]
  | CastE (t,e) ->
     LBLOCK [STR "caste ("; pe e; STR ":"; typ_to_pretty t; STR ")"]
  | AddrOf l -> LBLOCK [STR "addrof ("; pl l; STR ")"]
  | StartOf l -> LBLOCK [STR "startof ("; pl l; STR ")"]
  | FnApp (loc, e, el) ->
     LBLOCK [
         STR "fn(";
         pe e ;
         STR ")@ ";
         INT loc.line;
	 pretty_print_list el peo "[" ", " "]"]
  | CnApp (s, el, _t) ->
     begin
       match el with
       | [] -> STR s
       | _ -> LBLOCK [STR s ; pretty_print_list el peo "[" ", " "]"]
     end
  | _ -> cil_exp_to_pretty x


and opt_exp_to_pretty (e: bexp_t option) =
  match e with Some e -> exp_to_pretty e | _ -> STR "_"


and cil_lval_to_pretty ((host, offset): blval_t) =
  match (host, offset) with
  | (Var ((vname,_)),_) -> LBLOCK [STR vname; cil_offset_to_pretty offset]
  | (Mem e,_) ->
    LBLOCK [STR "*("; cil_exp_to_pretty e; STR ")"; cil_offset_to_pretty offset]


and lval_to_pretty ((host, offset): blval_t) =
  match (host, offset) with
  | (Var ((vname, _)), _) -> LBLOCK [STR vname; offset_to_pretty offset]
  | (Mem (Lval lval),NoOffset) -> LBLOCK [STR "(*"; lval_to_pretty lval; STR ")"]
  | (Mem (Lval lval),Field ((fname,_),offset1)) ->
     LBLOCK [ lval_to_pretty lval; STR "->"; STR fname; offset_to_pretty offset1]
  | _ -> cil_lval_to_pretty (host, offset)


and cil_offset_to_pretty (offset: boffset_t) =
  match offset with
  | NoOffset -> STR ""
  | Field ((fname,_),o) -> LBLOCK [STR "."; STR fname; cil_offset_to_pretty o]
  | Index (e,o) ->
     LBLOCK [STR "["; cil_exp_to_pretty e; STR "]"; cil_offset_to_pretty o]


and offset_to_pretty (offset: boffset_t) =
  match offset with
  | Field ((fname,_),offset1) ->
     LBLOCK [STR "."; STR fname; offset_to_pretty offset1]
  | Index (e,offset1) ->
     LBLOCK [STR "["; exp_to_pretty e; STR "]"; offset_to_pretty offset1]
  | _ -> cil_offset_to_pretty offset


let instr_to_pretty (instr: binstr_t) =
  match instr with
  | Set (lval, x, _loc) ->
     LBLOCK [
         STR "assign (";
         lval_to_pretty lval;
         STR ", ";
	 exp_to_pretty x;
         STR ")"]
  | Call (_optLval, _x, _args, _loc) -> LBLOCK [STR "call"]
  | VarDecl _ -> LBLOCK[STR "vardecl"]
  | Asm _ -> STR "asm"


let btype_to_pretty = typ_to_pretty

let btype_to_string = typ_to_string

let exp_to_string (e: bexp_t) = p2s (exp_to_pretty e)


let enuminfo_to_pretty (einfo: benuminfo_t) = STR einfo.bename


let varinfo_to_pretty (vinfo: bvarinfo_t) = STR vinfo.bvname


let fieldinfo_to_pretty (finfo: bfieldinfo_t) =
  let layout_to_pretty = match finfo.bfieldlayout with
    | Some (offset, size) ->
       LBLOCK [STR " // offset: "; INT offset; STR " size: "; INT size]
    | _ -> STR "" in
  LBLOCK [
      STR (btype_to_string finfo.bftype);
      STR " ";
      STR finfo.bfname;
      STR "; ";
      layout_to_pretty]


let compinfo_to_pretty (cinfo: bcompinfo_t) =
  let decl = if cinfo.bcstruct then "struct" else "union" in
  LBLOCK [
      STR decl;
      STR " ";
      STR cinfo.bcname;
      STR " {"; NL;
      LBLOCK
        (List.map (fun fieldinfo ->
             LBLOCK [STR "  "; fieldinfo_to_pretty fieldinfo; NL])
           cinfo.bcfields);
      STR "};"]

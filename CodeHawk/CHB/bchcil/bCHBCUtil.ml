(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHNumerical
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHUtil

(* bchcil *)
open BCHBCDictionary
open BCHCBasicTypes


let string_printer = CHPrettyUtil.string_printer
let p2s = string_printer#print


let bcd = BCHBCDictionary.bcdictionary


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
  | TFun (tt, optArgs, vararg, attrs) ->
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
  | CnApp (s,el,t) -> 
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
  | FnApp (loc,e,el) ->
     LBLOCK [
         STR "fn(";
         pe e ;
         STR ")@ ";
         INT loc.line; 
	 pretty_print_list el peo "[" ", " "]"]
  | CnApp (s,el,t) -> 
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
  | Set (lval,x,loc) -> 
     LBLOCK [
         STR "assign (";
         lval_to_pretty lval;
         STR ", ";
	 exp_to_pretty x;
         STR ")"]
  | Call (optLval,x,args,loc) -> LBLOCK [STR "call"]
  | VarDecl _ -> LBLOCK[STR "vardecl"]
  | Asm _ -> STR "asm"


let btype_to_pretty = typ_to_pretty
let btype_to_string = typ_to_string

let exp_to_string (e: bexp_t) = p2s (exp_to_pretty e)


let enuminfo_to_pretty (einfo: benuminfo_t) = STR einfo.bename
                                        
let compinfo_to_pretty (cinfo: bcompinfo_t) = STR cinfo.bcname

let varinfo_to_pretty (vinfo: bvarinfo_t) = STR vinfo.bvname
  
                              
let btype_equal (t1: btype_t) (t2: btype_t) =
  let i1 = bcd#index_typ t1 in
  let i2 = bcd#index_typ t2 in
  i1 = i2


(* --------------------------------- Comparison ----------------------- *)

let list_compare = CHUtil.list_compare


let attribute_compare a1 a2 =
  match (a1, a2) with (Attr (s1, _), Attr (s2, _)) -> Stdlib.compare s1 s2


let attributes_compare l1 l2 = list_compare l1 l2 attribute_compare


let rec typ_compare t1 t2 =
  match (t1,t2) with
  | (TUnknown attrs1,TUnknown attrs2) -> attributes_compare attrs1 attrs2
  | (TUnknown _,_) -> -1
  | (_, TUnknown _) -> 1
  | (TVoid attrs1,TVoid attrs2) -> attributes_compare attrs1 attrs2
  | (TVoid _,_) -> -1
  | (_, TVoid _) -> 1
  | (TInt (i1,attrs1), TInt (i2,attrs2)) -> 
     let l0 = Stdlib.compare i1 i2 in
     if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TInt _, _) -> -1
  | (_, TInt _) -> 1
  | (TFloat (f1,r1,attrs1), TFloat (f2,r2,attrs2)) -> 
    let l0 = Stdlib.compare f1 f2 in
    if l0 = 0 then 
      let l1 = Stdlib.compare r1 r2 in
      if l1 = 0 then
	attributes_compare attrs1 attrs2 
      else l1
    else l0
  | (TFloat _, _) -> -1
  | (_, TFloat _) -> 1
  | (TPtr (tt1,attrs1), TPtr (tt2,attrs2)) -> 
    let l0 = typ_compare tt1 tt2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TPtr _, _) -> -1
  | (_, TPtr _) -> 1
  | (TRef (tt1,attrs1), TRef (tt2,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TRef _,_) -> -1
  | (_, TRef _) -> 1
  | (THandle (s1,attrs1),THandle (s2,attrs2)) -> 
    let l0 = Stdlib.compare s1 s2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (THandle _,_) -> -1
  | (_, THandle _) -> 1
  | (TArray (tt1,x1,attrs1), TArray (tt2,x2,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in	
    if l0 = 0 then 
      let l1 = opt_exp_compare x1 x2 in
      if l1 = 0 then 
	attributes_compare attrs1 attrs2 
      else l1
    else l0
  | (TArray _, _) -> -1
  | (_, TArray _) -> 1
  | (TFun (tt1,args1,_,attrs1), TFun (tt2,args2,_,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in 
    if l0 = 0 then 
      let l1 = opt_arg_list_compare args1 args2 in
      if l1 = 0 then 
	attributes_compare attrs1 attrs2
      else l1 
    else l0
  | (TFun _, _) -> -1
  | (_, TFun _) -> 1
  | (TNamed (n1,attrs1), TNamed (n2,attrs2)) -> 
    let l0 = Stdlib.compare n1 n2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TNamed _,_) -> -1
  | (_, TNamed _) -> 1
  | (TComp (ckey1, attrs1), TComp (ckey2, attrs2)) -> 
    let l0 = Stdlib.compare ckey1 ckey2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TComp _, _) -> -1
  | (_, TComp _) -> 1
  | (TEnum (ename1, attrs1), TEnum (ename2, attrs2)) -> 
    let l0 = Stdlib.compare ename1 ename2 in 
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TEnum _, _) -> -1
  | (_, TEnum _) -> 1
  | (TClass (n1, ns1, attrs1), TClass (n2, ns2, attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then 
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TClass _, _) -> -1
  | (_, TClass _) -> 1
  | (TCppComp (n1, ns1, attrs1), TCppComp (n2, ns2, attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then 
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TCppComp _, _) -> -1
  | (_, TCppComp _) -> 1
  | (TCppEnum (n1, ns1, attrs1), TCppEnum (n2, ns2, attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then 
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TCppEnum _, _) -> -1
  | (_, TCppEnum _) -> 1
  | (TBuiltin_va_list a1, TBuiltin_va_list a2) -> attributes_compare a1 a2
  | (TBuiltin_va_list _, _) -> -1
  | (_, TBuiltin_va_list _) -> 1
  | (TVarArg attrs1, TVarArg attrs2) -> attributes_compare attrs1 attrs2


and tname_compare t1 t2 =
  match (t1,t2) with
  | (SimpleName n1, SimpleName n2) -> Stdlib.compare n1 n2
  | (SimpleName _,_) -> -1
  | (_, SimpleName _) -> 1
  | (TemplatedName (b1,args1), TemplatedName (b2,args2)) ->
    let l0 = tname_compare b1 b2 in
    if l0 = 0 then list_compare args1 args2 typ_compare else l0


and opt_arg_list_compare (a1: bfunarg_t list option) (a2: bfunarg_t list option) =
  match (a1, a2) with
  | (Some l1, Some l2) ->
     list_compare l1 l2 (fun (_, t1, _) (_, t2, _) -> typ_compare t1 t2)
  | (Some _, _) -> -1
  | (_, Some _) -> 1
  | _ -> 0


and opt_exp_compare (e1: bexp_t option) (e2: bexp_t option) =
  CHUtil.optvalue_compare e1 e2 exp_compare


and exp_compare e1 e2 =
  match (e1,e2) with
  | (Const c1, Const c2) -> constant_compare c1 c2
  | (Const _, _) -> -1
  | (_, Const _) -> 1
  | (Lval l1, Lval l2) -> lval_compare l1 l2
  | (Lval _, _) -> -1
  | (_, Lval _) -> 1
  | (SizeOf t1, SizeOf t2) -> typ_compare t1 t2
  | (SizeOf _, _) -> -1
  | (_, SizeOf _) -> 1
  | (Real e1, Real e2) -> exp_compare e1 e2
  | (Real _, _) -> -1
  | (_, Real _) -> 1
  | (Imag e1, Imag e2) -> exp_compare e1 e2
  | (Imag _, _) -> -1
  | (_, Imag _) -> 1
  | (SizeOfE e1, SizeOfE e2) -> exp_compare e1 e2
  | (SizeOfE _, _) -> -1
  | (_, SizeOfE _) -> 1
  | (SizeOfStr s1, SizeOfStr s2) -> Stdlib.compare s1 s2
  | (SizeOfStr _, _) -> -1
  | (_, SizeOfStr _) -> 1
  | (AlignOf t1, AlignOf t2) -> typ_compare t1 t2
  | (AlignOf _, _) -> -1
  | (_, AlignOf _) -> 1
  | (AlignOfE e1, AlignOfE e2) -> exp_compare e1 e2
  | (AlignOfE _, _) -> -1
  | (_, AlignOfE _) -> 1
  | (UnOp (op1, e1, t1), UnOp (op2, e2, t2)) ->
     let l0 = Stdlib.compare op1 op2 in
     if l0 = 0 then
       let l1 = exp_compare e1 e2 in
       if l1 = 0 then
         typ_compare t1 t2
       else
         l1
     else
       l0
  | (UnOp _, _) -> -1
  | (_, UnOp _) -> 1
  | (BinOp (op1, e11, e21, t1), BinOp (op2, e12, e22, t2)) ->
     let l0 = Stdlib.compare op1 op2 in
     if l0 = 0 then
       let l1 = exp_compare e11 e12 in
       if l1 = 0 then
         let l2 = exp_compare e21 e22 in
         if l2 = 0 then
           typ_compare t1 t2
         else
           l2
       else
         l1
     else
       l0
  | (BinOp _, _) -> -1
  | (_, BinOp _) -> 1
  | (Question (e11, e21, e31, t1), Question (e12, e22, e32, t2)) ->
     let l0 = exp_compare e11 e12 in
     if l0 = 0 then
       let l1 = exp_compare e21 e22 in
       if l1 = 0 then
         let l2 = exp_compare e31 e32 in
         if l2 = 0 then
           typ_compare t1 t2
         else
           l2
       else
         l1
     else
       l0
  | (Question _, _) -> -1
  | (_, Question _) -> 1
  | (CastE (t1, e1), CastE (t2, e2)) ->
     let l0 = typ_compare t1 t2 in
     if l0 = 0 then
       exp_compare e1 e2
     else
       l0
  | (CastE _, _) -> -1
  | (_, CastE _) -> 1
  | (AddrOf l1, AddrOf l2) -> lval_compare l1 l2
  | (AddrOf _, _) -> -1
  | (_, AddrOf _) -> 1
  | (AddrOfLabel l1, AddrOfLabel l2) -> Stdlib.compare l1 l2
  | (AddrOfLabel _, _) -> -1
  | (_, AddrOfLabel _) -> 1
  | (StartOf l1, StartOf l2) -> lval_compare l1 l2
  | (StartOf _, _) -> -1
  | (_, StartOf _) -> 1
  | (FnApp (_, e1, e1l), FnApp (_, e2, e2l)) ->
     let l0 = exp_compare e1 e2 in
     if l0 = 0 then
       opt_exp_list_compare e1l e2l
     else
       l0
  | (FnApp _, _) -> -1
  | (_, FnApp _) -> 1
  | (CnApp (s1, e1l, t1), CnApp (s2, e2l, t2)) ->
     let l0 = Stdlib.compare s1 s2 in
     if l0 = 0 then
       let l1 = opt_exp_list_compare e1l e2l in
       if l1 = 0 then
         typ_compare t1 t2
       else
         l1
     else
       l0


and opt_exp_list_compare (l1: (bexp_t option) list) (l2: (bexp_t option) list) =
  list_compare l1 l2 opt_exp_compare


and lval_compare (lv1: blval_t) (lv2: blval_t) =
  match (lv1, lv2) with
  | ((h1, o1), (h2, o2)) ->
     let l0 = lhost_compare h1 h2 in
     if l0 = 0 then
       offset_compare o1 o2
     else
       l0


and lhost_compare (h1: blhost_t) (h2: blhost_t) =
  match (h1, h2) with
  | (Var v1, Var v2) -> Stdlib.compare v1 v2
  | (Var _, _) -> -1
  | (_, Var _) -> 1
  | (Mem e1, Mem e2) -> exp_compare e1 e2


and offset_compare (o1: boffset_t) (o2: boffset_t) =
  match (o1, o2) with
  | (NoOffset, NoOffset) -> 0
  | (NoOffset, _) -> -1
  | (_, NoOffset) -> 1
  | (Field (f1, oo1), Field (f2, oo2)) ->
     let l0 = Stdlib.compare f1 f2 in
     if l0 = 0 then
       offset_compare oo1 oo2
     else
       l0
  | (Field _, _) -> -1
  | (_, Field _) -> 1
  | (Index (e1, oo1), Index (e2, oo2)) ->
     let l0 = exp_compare e1 e2 in
     if l0 = 0 then
       offset_compare oo1 oo2
     else
       l0


and constant_compare c1 c2 =
  match (c1,c2) with
  | (CInt (i1,k1,_), CInt (i2,k2,_)) ->
    let l0 = Int64.compare i1 i2 in if l0 = 0 then Stdlib.compare k1 k2 else l0
  | (CInt _, _) -> -1
  | (_, CInt _) -> 1
  | (CStr s1, CStr s2) -> Stdlib.compare s1 s2
  | (CStr _, _) -> -1
  | (_, CStr _) -> 1
  | (CWStr l1, CWStr l2) ->  list_compare l1 l2 Int64.compare
  | (CWStr _, _) -> -1
  | (_, CWStr _) -> 1
  | (CChr c1, CChr c2) -> Char.compare c1 c2
  | (CChr _, _) -> -1
  | (_, CChr _) -> 1
  | (CReal (f1,_,_), CReal (f2,_,_)) -> Stdlib.compare f1 f2
  | (CReal _, _) -> -1
  | (_, CReal _) -> 1
  | (CEnum (e1,iname1,ename1), CEnum (e2,iname2,ename2)) ->
    let l0 = Stdlib.compare iname1 iname2 in
    if l0 = 0 then 
      let l1 = Stdlib.compare ename1 ename2 in
      if l1 = 0 then
	exp_compare e1 e2
      else l1
    else l0


let btype_compare = typ_compare
                                 

let add_attributes (t: btype_t) (a: b_attributes_t) =
  match t with
  | TVoid aa -> TVoid (aa @ a)
  | TInt (ik, aa) -> TInt (ik, aa @ a)
  | TFloat (fk, fr, aa) -> TFloat (fk, fr, aa @ a)
  | TPtr (tt, aa) -> TPtr (tt, aa @ a)
  | TRef (tt, aa) -> TRef (tt, aa @ a)
  | THandle (s, aa) -> THandle (s, aa @ a)
  | TArray (tt, e, aa) -> TArray (tt, e, aa @ a)
  | TFun (tt, l, b, aa) -> TFun (tt, l, b, aa @ a)
  | TNamed (s, aa) -> TNamed (s, aa @ a)
  | TComp (k, aa) -> TComp (k, aa @ a)
  | TEnum (s, aa) -> TEnum (s, aa @ a)
  | TCppComp (s, sl, aa) -> TCppComp (s, sl, aa @ a)
  | TCppEnum (s, sl, aa) -> TCppEnum (s, sl, aa @ a)
  | TClass (s, sl, aa) -> TClass (s, sl, aa @ a)
  | TBuiltin_va_list aa -> TBuiltin_va_list (aa @ a)
  | TVarArg aa -> TVarArg (aa @ a)
  | TUnknown aa -> TUnknown (aa @ a)

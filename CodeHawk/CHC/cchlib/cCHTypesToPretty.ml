(* =============================================================================
   CodeHawk C Analyzer 
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
open CHNumerical
open CHPretty

(* chutil *)
open CHPrettyUtil

(* cchlib *)
open CCHBasicTypes
open CCHDictionary

let string_printer = CHPrettyUtil.string_printer
let p2s = string_printer#print

let cd = CCHDictionary.cdictionary

let location_line_to_string (loc:location) =
  loc.file ^ "@" ^ (string_of_int loc.line)

let storage_to_string (s:storage) =
  match s with
  | NoStorage -> ""
  | Static -> "static"
  | Register -> "register"
  | Extern -> "extern"
  | Opaque i -> "opaque_" ^  (string_of_int i)

let location_to_pretty (loc:location) =
  LBLOCK [ STR loc.file ; STR " @ " ; INT loc.line ; STR " (" ; INT loc.byte ; STR ")" ]

let int_type_to_string (k:ikind) =
  match k with
  | IChar -> "char"
  | ISChar -> "signed char"
  | IUChar -> "unsigned char"
  | IBool -> "bool"
  | IInt -> "int"
  | IUInt -> "unsigned int"
  | IShort -> "short"
  | IUShort -> "unsigned short"
  | ILong -> "long"
  | IULong -> "unsigned long"
  | ILongLong -> "long long"
  | IULongLong -> "unsigned long long"
    
let unop_to_print_string (op:unop) =
  match op with
  | Neg -> " - "
  | BNot -> " ~ "
  | LNot -> " ! "
    
let binop_to_print_string (op:binop) =
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
    
let float_type_to_string (k:fkind) =
  match k with
  | FFloat -> "float"
  | FDouble -> "double"
  | FLongDouble -> "long double"
    
let cil_constant_to_string (c:constant) =
  match c with
  | CInt64 (_,_,Some t) -> t
  | CInt64 (i64,_,_) -> Int64.to_string i64
  | CStr s ->
     let (_,_,len) = mk_constantstring s in
     (string_of_int len) ^ "-char-string-literal"
  | CWStr l64 -> String.concat " " (List.map Int64.to_string l64)
  | CChr c -> string_of_int (Char.code c)
  | CReal (_,_,Some t) -> t
  | CReal (f,_,_)  -> string_of_float f
  | CEnum (_,s,_) -> s

let constant_to_string (c:constant) =
  match c with
  | CStr s ->
     let (_,_,len) = mk_constantstring s in
     (string_of_int len) ^ "-char-string"
  | _ -> cil_constant_to_string c
    
let rec typ_to_string (t:typ) =
  match t with
  | TVoid _ -> "void"
  | TInt (ikind,_) -> int_type_to_string ikind
  | TFloat (fkind,_) -> float_type_to_string fkind
  | TPtr (tt,_) -> "(" ^ (typ_to_string tt) ^ "*)"
  | TArray (tt,Some x,_) ->
     (typ_to_string tt) ^ "[" ^ (p2s (exp_to_pretty x)) ^ "]"
  | TArray (tt,None,_) -> (typ_to_string tt) ^ "[]"
  | TFun (tt,optArgs,vararg,_) -> "function-pointer"
  | TNamed (name,_) -> name
  | TComp (key,_) -> "struct " ^ (string_of_int key)
  | TEnum (name,_) -> "enum " ^ name
  | TBuiltin_va_list _ -> "builtin_va_list"
    
and typ_to_pretty (t:typ) = STR (typ_to_string t)
  
and cil_exp_to_pretty (x:exp) =
  let pe = cil_exp_to_pretty in
  let pl = cil_lval_to_pretty in
  let peo = opt_cil_exp_to_pretty in
  match x with
  | Const c -> STR (cil_constant_to_string c)
  | Lval l -> LBLOCK [ STR "lval (" ; pl l ; STR ")" ]
  | SizeOf t -> LBLOCK [ STR "sizeof (" ; typ_to_pretty t ; STR ")" ]
  | SizeOfE e -> LBLOCK [ STR "sizeofe (" ; pe e ; STR ")" ]
  | SizeOfStr s ->
     let (_,_,len) = mk_constantstring s in
     LBLOCK [ STR "sizeofstr (" ; INT len ; STR "-char-string)" ]
  | AlignOf t -> LBLOCK [ STR "alignof (" ;  typ_to_pretty t ; STR ")" ]
  | AlignOfE e -> LBLOCK [ STR "alignofe (" ; pe e ; STR ")" ]
  | UnOp (op,e,t) -> 
    LBLOCK [ STR "((" ; STR (unop_to_print_string op) ; STR " " ; pe e ; 
	     STR "):" ; typ_to_pretty t ; STR ")" ]
  | BinOp (op,e1,e2,t) ->
    LBLOCK [ STR "((" ; pe e1 ; STR (binop_to_print_string op) ; pe e2 ;
	     STR "):" ; typ_to_pretty t ]
  | Question (e1,e2,e3,t) ->
    LBLOCK [ STR "((" ; pe e1 ; STR " ? " ; pe e2 ; STR " : " ;
	     pe e3 ; STR "):" ; typ_to_pretty t ; STR ")" ]
  | CastE (t,e) -> LBLOCK [ STR "caste (" ; pe e ; STR ":" ; typ_to_pretty t ; STR ")" ]
  | AddrOf l -> LBLOCK [ STR "addrof (" ; pl l ; STR ")" ]
  | AddrOfLabel l -> LBLOCK [ STR "addroflabel (" ; INT l ; STR ")" ]
  | StartOf l -> LBLOCK [ STR "startof (" ; pl l ; STR ")" ]
  | FnApp (loc,e,el) -> LBLOCK [ STR "fn(" ; pe e ; STR ")@ " ; INT loc.line ; 
				 pretty_print_list el peo "[" ", " "]" ]
  | CnApp (s,el,t) -> 
    begin
      match el with
      | [] -> STR s
      | _ -> LBLOCK [ STR s ; pretty_print_list el peo "[" ", " "]" ]
    end
    
and opt_cil_exp_to_pretty (e:exp option) = 
  match e with Some e -> exp_to_pretty e | _ -> STR "_"

and exp_to_pretty (x:exp) =
  let pe = exp_to_pretty in
  let pl = lval_to_pretty in
  let peo = opt_exp_to_pretty in
  match x with
  | CastE (_, CastE (TPtr (TVoid _,_),Const (CInt64 (i64,_,_))))
       when (mkNumericalFromInt64 i64)#equal numerical_zero -> STR "NULL"
  | Const c -> STR (constant_to_string c)
  | Lval l -> pl l
  | SizeOfE e -> LBLOCK [ STR "sizeof(" ; pe e ; STR ")" ]
  | AlignOfE e -> LBLOCK [ STR "alignof(" ; pe e ; STR ")" ]
  | UnOp (op,e,t) -> 
    LBLOCK [ STR "((" ; STR (unop_to_print_string op) ; STR " " ; pe e ; 
	     STR "):" ; typ_to_pretty t ; STR ")" ]
  | BinOp (op,e1,e2,t) ->
    LBLOCK [ STR "((" ; pe e1 ; STR (binop_to_print_string op) ; pe e2 ;
	     STR "):" ; typ_to_pretty t ]
  | CastE (t,e) -> 
    LBLOCK [ STR "caste (" ; pe e ; STR ":" ; typ_to_pretty t ; STR ")" ]
  | AddrOf l -> LBLOCK [ STR "addrof (" ; pl l ; STR ")" ]
  | StartOf l -> LBLOCK [ STR "startof (" ; pl l ; STR ")" ]
  | FnApp (loc,e,el) -> LBLOCK [ STR "fn(" ; pe e ; STR ")@ " ; INT loc.line ; 
				 pretty_print_list el peo "[" ", " "]" ]
  | CnApp (s,el,t) -> 
    begin
      match el with
      | [] -> STR s
      | _ -> LBLOCK [ STR s ; pretty_print_list el peo "[" ", " "]" ]
    end
  | _ -> cil_exp_to_pretty x
  
and opt_exp_to_pretty (e:exp option) = 
  match e with Some e -> exp_to_pretty e | _ -> STR "_"
  
and cil_lval_to_pretty ((host,offset):lval) =
  match (host,offset) with
  | (Var ((vname,_)),_) -> LBLOCK [ STR vname ; cil_offset_to_pretty offset ]
  | (Mem e,_) -> 
    LBLOCK [ STR "*(" ; cil_exp_to_pretty e  ; STR ")" ; cil_offset_to_pretty offset ]

and lval_to_pretty ((host,offset):lval) =
  match (host,offset) with
  | (Var ((vname,_)),_) -> LBLOCK [ STR vname ; offset_to_pretty offset ]
  | (Mem (Lval lval),NoOffset) -> LBLOCK [ STR "(*" ; lval_to_pretty lval ; STR ")" ]
  | (Mem (Lval lval),Field ((fname,_),offset1)) ->
    LBLOCK [ lval_to_pretty lval ; STR "->" ; STR fname ; offset_to_pretty offset1 ]
  | _ -> cil_lval_to_pretty (host,offset)
    
and cil_offset_to_pretty offset =
  match offset with
  | NoOffset -> STR ""
  | Field ((fname,_),o) -> LBLOCK [ STR "." ; STR fname ; cil_offset_to_pretty o ]
  | Index (e,o) -> 
    LBLOCK [ STR "[" ; cil_exp_to_pretty e ; STR "]" ; cil_offset_to_pretty o ]

and offset_to_pretty offset =
  match offset with
  | Field ((fname,_),offset1) -> 
    LBLOCK [ STR "." ; STR fname ; offset_to_pretty offset1 ]
  | Index (e,offset1) -> 
    LBLOCK [ STR "[" ; exp_to_pretty e ; STR "]" ; offset_to_pretty offset1 ]
  | _ -> cil_offset_to_pretty offset
    
let instr_to_pretty (instr:instr) =
  match instr with
  | Set (lval,x,loc) -> 
    LBLOCK [ STR "assign (" ; lval_to_pretty lval ; STR ", " ;
	     exp_to_pretty x ; STR ")" ]
  | Call (optLval,x,args,loc) -> LBLOCK [ STR "call" ]
  | Asm _ -> STR "asm"
    
let enuminfo_to_pretty (einfo:enuminfo) = STR einfo.ename
let compinfo_to_pretty (cinfo:compinfo) = STR cinfo.cname
let varinfo_to_pretty (vinfo:varinfo) = STR vinfo.vname
  

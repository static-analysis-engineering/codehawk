(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
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

(* cil *)
open Cil

(* cchcil *)
open CHPrettyPrint
open CHUtilities

module H = Hashtbl

class type ['a] sumtype_string_converter_int =
  object
    method to_string: 'a -> string
    method from_string: string -> 'a
  end

class ['a] sumtype_string_converter_t
           (name:string) (pairs:('a * string) list):['a] sumtype_string_converter_int =
object

  val tstable = H.create (List.length pairs)
  val sttable = H.create (List.length pairs)

  initializer
    List.iter (fun (t,s) -> begin H.add tstable t s ; H.add sttable s t end) pairs

  method to_string (t:'a) =
    if H.mem tstable t then
      H.find tstable t
    else
      raise (CCFailure (LBLOCK [ STR "Type not found for sumtype " ; STR name ]))

  method from_string (s:string) =
    if H.mem sttable s then
      H.find sttable s
    else
      raise (CCFailure (LBLOCK [ STR "No sumtype " ; STR name ;
                                  STR " for string " ; STR s ]))

end

let mk_sumtype_string_converter = new sumtype_string_converter_t

let ikind_serializer: ikind sumtype_string_converter_int =
  mk_sumtype_string_converter
    "ikind"
    [ (IChar, "ichar"); (ISChar, "ischar"); (IUChar, "iuchar");
      (IBool, "ibool"); (IInt, "iint"); (IUInt, "iuint");
      (IShort, "ishort"); (IUShort, "iushort"); (ILong, "ilong");
      (IULong, "iulong"); (ILongLong, "ilonglong");
      (IULongLong, "iulonglong") ]

let fkind_serializer: fkind sumtype_string_converter_int =
  mk_sumtype_string_converter
    "fkind"
    [ (FFloat, "float"); (FDouble, "fdouble"); (FLongDouble, "flongdouble") ]

let unop_serializer: unop sumtype_string_converter_int =
  mk_sumtype_string_converter
    "unop"  [ (Neg, "neg"); (BNot, "bnot"); (LNot, "lnot") ]

let binop_serializer: binop sumtype_string_converter_int =
  mk_sumtype_string_converter
  "binop"
  [ (PlusA, "plusa"); (PlusPI, "pluspi"); (IndexPI, "indexpi");
    (MinusA, "minusa"); (MinusPI, "minuspi"); (MinusPP, "minuspp");
    (Mult, "mult"); (Div, "div"); (Mod, "mod"); (Shiftlt, "shiftlt");
    (Shiftrt, "shiftrt"); (Lt, "lt"); (Gt, "gt"); (Le, "le");
    (Ge, "ge"); (Eq, "eq"); (Ne, "ne"); (BAnd, "band"); (BXor, "bxor");
    (BOr, "bor"); (LAnd, "land"); (LOr, "lor") ]

let storage_serializer: storage sumtype_string_converter_int =
  mk_sumtype_string_converter
    "storage"
    [ (NoStorage,"n"); (Static,"s"); (Register,"r"); (Extern,"x") ]


class virtual ['a] complextyp_string_converter_t (name:string) =
object

  method virtual to_string: 'a -> string

  method from_string (s:string):'a =
    raise (CCFailure (LBLOCK [ STR "No reverse construction possible for " ; STR name ]))

end

class typ_string_converter_t:[typ] sumtype_string_converter_int =
object

  inherit [typ] complextyp_string_converter_t "typ"
  
  method to_string (t:typ) =
    match t with
    | TVoid _ -> "tvoid"
    | TInt _ -> "tint"
    | TFloat _ -> "tfloat"
    | TPtr _ -> "tptr"
    | TArray _ -> "tarray"
    | TFun _ -> "tfun"
    | TNamed _ -> "tnamed"
    | TComp _ -> "tcomp"
    | TEnum _ -> "tenum"
    | TBuiltin_va_list _ -> "tbuiltin-va-list"

end

let typ_serializer: typ sumtype_string_converter_int = new typ_string_converter_t


class exp_string_converter_t:[exp] sumtype_string_converter_int =
object

  inherit [exp] complextyp_string_converter_t "exp"

  method to_string (e:exp) =
    match e with
    | Const _ -> "const"
    | Lval _ -> "lval"
    | SizeOf _ -> "sizeof"
    | SizeOfE _ -> "sizeofe"
    | SizeOfStr _ -> "sizeofstr"
    | AlignOf _ -> "alignof"
    | AlignOfE _ -> "alignofe"
    | UnOp _ -> "unop"
    | BinOp _ -> "binop"
    | Question _ -> "question"
    | CastE _ -> "caste"
    | AddrOf _ -> "addrof"
    | AddrOfLabel _ -> "addroflabel"
    | StartOf _ -> "startof"

end

let exp_serializer:exp sumtype_string_converter_int =
  new exp_string_converter_t

    
class attrparam_string_converter_t:[attrparam] sumtype_string_converter_int =
object

  inherit [attrparam] complextyp_string_converter_t "attrparam"

  method to_string (a:attrparam) =
    match a with
    | AInt _ -> "aint"
    | AStr _ -> "astr"
    | ACons _ -> "acons"
    | ASizeOf _ -> "asizeof"
    | ASizeOfE _ -> "asizeofe"
    | ASizeOfS _ -> "asizeofs"
    | AAlignOf _ -> "aalignof"
    | AAlignOfE _ -> "aalignofe"
    | AAlignOfS _ -> "aalignofs"
    | AUnOp _ -> "aunop"
    | ABinOp _ -> "abinop"
    | ADot _ -> "adot"
    | AStar _ -> "astar"
    | AAddrOf _ -> "aaddrof"
    | AIndex _ -> "aindex"
    | AQuestion _ -> "aquestion"

end

let attrparam_serializer: attrparam sumtype_string_converter_int =
  new attrparam_string_converter_t

class constant_string_converter_t:[constant] sumtype_string_converter_int =
object

  inherit [constant] complextyp_string_converter_t "constant"

  method to_string (c:constant) =
    match c with
    | CInt64 _ -> "int"
    | CStr _ -> "str"
    | CWStr _ -> "wstr"
    | CChr _ -> "chr"
    | CReal _ -> "real"
    | CEnum _ -> "enum"

end

let constant_serializer: constant sumtype_string_converter_int =
  new constant_string_converter_t
  

class offset_string_converter_t:[offset] sumtype_string_converter_int =
object

  inherit [offset] complextyp_string_converter_t "offset"

  method to_string (o:offset) =
    match o with
    | NoOffset -> "n"
    | Field _ -> "f"
    | Index _ -> "i"

end

let offset_serializer: offset sumtype_string_converter_int =
  new offset_string_converter_t


class typsig_string_converter_t:[typsig] sumtype_string_converter_int =
object

  inherit [typsig] complextyp_string_converter_t "typsig"

  method to_string (t:typsig) =
    match t with
    | TSArray _ -> "tsarray"
    | TSPtr _ -> "tsptr"
    | TSComp _ -> "tscomp"
    | TSFun _ -> "tsfun"
    | TSEnum _ -> "tsenum"
    | TSBase _ -> "tsbase"
end

let typsig_serializer:typsig sumtype_string_converter_int =
  new typsig_string_converter_t
        
  
class label_string_converter_t:[label] sumtype_string_converter_int =
object

  inherit [label] complextyp_string_converter_t "label"

  method to_string (l:label) =
    match l with
    | Label _ -> "label"
    | Case _ -> "case"
    | CaseRange _ -> "caserange"
    | Default _ -> "default"

end

let label_serializer:label sumtype_string_converter_int =
  new label_string_converter_t

class stmtkind_string_converter_t:[stmtkind] sumtype_string_converter_int =
object

  inherit [stmtkind] complextyp_string_converter_t "stmtkind"

  method to_string (s:stmtkind) =
    match s with
    | Instr _ -> "instr"
    | Return _ -> "return"
    | Goto _ -> "goto"
    | ComputedGoto _ -> "computedgoto"
    | Break _ -> "break"
    | Continue _ -> "continue"
    | If _ -> "if"
    | Switch _ -> "switch"
    | Loop _ -> "loop"
    | Block _ -> "block"
    | TryFinally _ -> "tryfinally"
    | TryExcept _ -> "tryexcept"
    
end

let stmtkind_serializer:stmtkind sumtype_string_converter_int =
  new stmtkind_string_converter_t

class instr_string_converter_t:[instr] sumtype_string_converter_int =
object

  inherit [instr] complextyp_string_converter_t "instr"

  method to_string (i:instr) =
    match i with
    | Set _ -> "set"
    | Call _ -> "call"
    | Asm _ -> "asm"

end

let instr_serializer:instr sumtype_string_converter_int =
  new instr_string_converter_t

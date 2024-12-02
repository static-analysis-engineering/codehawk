(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* ============================================================================== *
 * The data types used here are very close to the CIL data types. Some fields or  *
 * selectors that seem to be primarily used for transformation have been removed. *
 * ============================================================================== *)

(* chutil *)
open CHXmlDocument

type ikind =
| IChar       (** [char] *)
| ISChar      (** [signed char] *)
| IUChar      (** [unsigned char] *)
| IBool       (** [_Bool (C99)] *)
| IInt        (** [int] *)
| IUInt       (** [unsigned int] *)
| IShort      (** [short] *)
| IUShort     (** [unsigned short] *)
| ILong       (** [long] *)
| IULong      (** [unsigned long] *)
| ILongLong   (** [long long] (or [_int64] on Microsoft Visual C) *)
| IULongLong  (** [unsigned long long] (or [unsigned _int64] on Microsoft
                  Visual C) *)
| IInt128     (** added by Goblint-Cil *)
| IUInt128    (** added by Goblint-Cil *)


(** Various kinds of floating-point numbers*)
type fkind =
| FFloat      (** [float] *)
| FDouble     (** [double] *)
| FLongDouble (** [long double] *)
| FComplexFloat
| FComplexDouble
| FComplexLongDouble


type storage =
| NoStorage
| Static
| Register
| Extern
| Opaque of int

type unop =
| Neg
| BNot
| LNot

type binop =
| PlusA
| PlusPI
| IndexPI
| MinusA
| MinusPI
| MinusPP
| Mult
| Div
| Mod
| Shiftlt
| Shiftrt
| Lt
| Gt
| Le
| Ge
| Eq
| Ne
| BAnd
| BXor
| BOr
| LAnd
| LOr

type varuse = string * int      (* vname, vid *)

type fielduse = string * int    (* fname, fckey *)

type typ =
| TVoid of attributes
| TInt of ikind * attributes
| TFloat of fkind * attributes
| TPtr of typ * attributes
| TArray of typ * exp option * attributes
| TFun of typ * funarg list option * bool * attributes
| TNamed of string * attributes
| TComp of int * attributes
| TEnum of string * attributes
| TBuiltin_va_list of attributes

and funarg = string * typ * attributes

and attribute = Attr of string  * attrparam list

and attributes = attribute list

and attrparam =
| AInt of int
| AStr of string
| ACons of string * attrparam list
| ASizeOf of typ
| ASizeOfE of attrparam
| ASizeOfS of typsig
| AAlignOf of typ
| AAlignOfE of attrparam
| AAlignOfS of typsig
| AUnOp of unop * attrparam
| ABinOp of binop * attrparam * attrparam
| ADot of attrparam * string
| AStar of attrparam
| AAddrOf of attrparam
| AIndex of attrparam * attrparam
| AQuestion of attrparam * attrparam * attrparam
| AAssign of attrparam * attrparam

and compinfo = {
  cstruct: bool ;
  cname  : string ;
  ckey   : int ;
  cfields: fieldinfo list ;
  cattr  : attributes ;
}

and fieldinfo = {
  fckey    : int ;   (* key of the containing compinfo *)
  fname    : string ;
  ftype    : typ ;
  fbitfield: int option ;
  fattr    : attributes ;
  floc     : location
}

and eitem = string * attributes * exp * location

and enuminfo = {
  ename    : string ;
  eitems   : eitem list ;
  eattr    : attributes ;
  ekind    : ikind ;
}

and typeinfo = {
  tname    : string ;
  ttype    : typ ;
}

and varinfo = {
  vname    : string ;
  vtype    : typ ;
  vstorage : storage ;
  vglob    : bool ;
  vinline  : bool ;
  vdecl    : location ;
  vinit    : initinfo ;
  vid      : int ;
  vattr    : attributes ;
  vaddrof  : bool ;
  vparam   : int    (* 0 for local/global variables, seqnr for parameters *)
}

and exp =
| Const of constant
| Lval of lval
| SizeOf of typ
| SizeOfE of exp
| SizeOfStr of string
| AlignOf of typ
| AlignOfE of exp
| UnOp of unop * exp * typ
| BinOp of binop * exp * exp * typ
| Question of exp * exp * exp * typ
| CastE of typ * exp
| AddrOf of lval
| AddrOfLabel of int
| StartOf of lval
| FnApp of location * exp * (exp option) list     (* program function application *)
| CnApp of string * exp option list * typ         (* constant, predefined function application *)

and constant =
| CInt of int64 * ikind * string option
| CStr of string
| CWStr of int64 list
| CChr of char
| CReal of float * fkind * string option
| CEnum of exp * string * string

and lval = lhost * offset

and lhost =
| Var of varuse
| Mem of exp

and offset =
| NoOffset
| Field of fielduse * offset
| Index of exp * offset

and init =
| SingleInit of exp
| CompoundInit of typ * (offset * init) list

and initinfo = init option

and block = {
  battrs  : attributes ;
  bstmts  : stmt list
}

and stmt = {
  labels  : label list ;
  skind   : stmtkind ;
  sid     : int ;
  succs   : int list ;
  preds   : int list
}

and label =
| Label of string * location * bool
| Case of exp * location
| CaseRange of exp * exp * location
| Default of location

and stmtkind =
| Instr of instr list
| Return of exp option * location
| Goto of int * location
| ComputedGoto of exp * location
| Break of location
| Continue of location
| If of exp * block * block * location
| Switch of exp * block * (int list) * location
| Loop of block * location * (int option) * (int option)   (* continue stmt, break stmt *)
| Block of block
| TryFinally of block * block * location
| TryExcept of block * (instr list * exp) * block * location

and asm_output_t = string option * string * lval (* name, constraint, lval *)

and asm_input_t = string option * string * exp (* name, constraint, exp *)

and instr =
| Set of lval * exp * location
| Call of lval option * exp * exp list * location
| VarDecl of varinfo * location
| Asm of
    attributes
    * int list
    * asm_output_t list
    * asm_input_t list
    * int list
    * location

and location = {
  line : int ;
  file : string ;
  byte : int
}

and typsig =
| TSArray of typsig * int64 option * attribute list
| TSPtr of typsig * attribute list
| TSComp of bool * string * attribute list
| TSFun of typsig * typsig list option * bool * attribute list
| TSEnum of string * attribute list
| TSBase of typ

type global =
| GType of typeinfo * location
| GCompTag of compinfo * location
| GCompTagDecl of compinfo * location
| GEnumTag of enuminfo * location
| GEnumTagDecl of enuminfo * location
| GVarDecl of varinfo *location
| GVar of varinfo * initinfo * location
| GFun of varinfo * location
| GAsm of string * location
| GPragma of attribute * location
| GText of string

class type cfundeclarations_int =
  object

    method index_formal: varinfo -> int
    method index_local : varinfo -> int
    method index_varinfo: varinfo -> int

    method get_formal  : int -> varinfo   (* seq number, starting at 1 *)
    method get_formals : varinfo list
    method get_locals  : varinfo list

    method get_varinfo_by_name: string -> varinfo
    method get_varinfo : int -> varinfo       (* index *)
    method get_varinfo_by_vid: int -> varinfo (* vid *)

    method is_formal : int -> bool            (* vid *)
    method is_local  : int -> bool            (* vid *)
    method has_varinfo: int -> bool           (* vid *)

    method read_xml : xml_element_int -> unit

  end

type fundec = {
    svar    : varinfo ;
    sdecls  : cfundeclarations_int ;
    sbody   : block
}


type file = {
  fileName: string ;
  globals: global list
}

(* =============================================================================
   CodeHawk Binary Analyzer 
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

(* ============================================================================== *
 * The data types used here are very close to the CIL data types. Some fields or  *
 * selectors that seem to be primarily used for transformation have been removed. *
 * ============================================================================== *)

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument


type constantstring = string * bool * int


type ikind_t = 
| IChar       (** [char] *)
| ISChar      (** [signed char] *)
| IUChar      (** [unsigned char] *)
| IWChar      (** [Windows, not in cil] *)
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
(** [local to binary analyzer, not in cil: signed, size in bytes] *)
| INonStandard of bool * int

		
(** Various kinds of floating-point numbers*)
type fkind_t = 
| FFloat      (** [float] *)
| FDouble     (** [double] *)
| FLongDouble (** [long double] *)

type frepresentation_t = FScalar | FPacked

type bstorage_t =
| NoStorage
| Static
| Register
| Extern
| Opaque of int

type unop_t =
| Neg
| BNot
| LNot

type binop_t =
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

type varuse_t = string * int      (* vname, vid *)

type fielduse_t = string * int    (* fname, fckey *)

type fieldlayout_t = int * int    (* offset, size (in bytes) *)

type type_transformer_t = string -> string

and btype_t =
| TVoid of b_attributes_t
| TInt of ikind_t * b_attributes_t
| TFloat of fkind_t * frepresentation_t * b_attributes_t
| TPtr of btype_t * b_attributes_t
| TRef of btype_t * b_attributes_t   (* not in cil *)
| THandle of string * b_attributes_t    (* not in cil *)
| TArray of btype_t * bexp_t option * b_attributes_t
| TFun of btype_t * bfunarg_t list option * bool * b_attributes_t
| TNamed of string * b_attributes_t
| TComp of int * b_attributes_t  
| TEnum of string * b_attributes_t
| TCppComp of tname_t * tname_t list * b_attributes_t  (* C++ name spaces *)
| TCppEnum of tname_t * tname_t list * b_attributes_t  (* C++ name spaces *)         
| TClass of tname_t * tname_t list * b_attributes_t  (* C++ name spaces, not in cil *)
| TBuiltin_va_list of b_attributes_t
| TVarArg of b_attributes_t
| TUnknown of b_attributes_t

and tname_t =
| SimpleName of string
| TemplatedName of tname_t * btype_t list  

and bfunarg_t = string * btype_t * b_attributes_t
		
and b_attribute_t = Attr of string  * b_attrparam_t list
		
and b_attributes_t = b_attribute_t list
	
and b_attrparam_t =
| AInt of int
| AStr of string
| ACons of string * b_attrparam_t list
| ASizeOf of btype_t
| ASizeOfE of b_attrparam_t
| ASizeOfS of btypsig_t
| AAlignOf of btype_t
| AAlignOfE of b_attrparam_t
| AAlignOfS of btypsig_t
| AUnOp of unop_t * b_attrparam_t
| ABinOp of binop_t * b_attrparam_t * b_attrparam_t
| ADot of b_attrparam_t * string
| AStar of b_attrparam_t
| AAddrOf of b_attrparam_t
| AIndex of b_attrparam_t * b_attrparam_t
| AQuestion of b_attrparam_t * b_attrparam_t * b_attrparam_t

and bcompinfo_t = {
  bcstruct: bool ;
  bcname: string ;
  bckey: int ;
  bcfields: bfieldinfo_t list ;
  bcattr: b_attributes_t ;
}

and bfieldinfo_t = {
  bfckey: int;   (* key of the containing compinfo *)
  bfname: string;
  bftype: btype_t;
  bfbitfield: int option;
  bfattr: b_attributes_t;
  bfloc: b_location_t;
  bfieldlayout: fieldlayout_t option
}
  
and beitem_t = string * bexp_t * b_location_t
  
and benuminfo_t = {
  bename: string;
  beitems: beitem_t list;
  beattr: b_attributes_t;
  bekind: ikind_t;
}
  
and btypeinfo_t = {
  btname: string;
  bttype: btype_t;
}
  
and bvarinfo_t = {
  bvname: string;
  bvtype: btype_t;
  bvstorage: bstorage_t;
  bvglob: bool;
  bvinline: bool;
  bvdecl: b_location_t;
  bvinit: binitinfo_t;
  bvid: int;
  bvattr: b_attributes_t;
  bvaddrof: bool;
  bvparam: int    (* 0 for local/global variables, seqnr for parameters *)
}
  
and bexp_t =
| Const of bconstant_t
| Lval of blval_t
| SizeOf of btype_t
| SizeOfE of bexp_t
| SizeOfStr of string
| AlignOf of btype_t
| AlignOfE of bexp_t
| UnOp of unop_t * bexp_t * btype_t
| BinOp of binop_t * bexp_t * bexp_t * btype_t
| Question of bexp_t * bexp_t * bexp_t * btype_t
| CastE of btype_t * bexp_t
| AddrOf of blval_t
| AddrOfLabel of int
| StartOf of blval_t
| FnApp of
    b_location_t * bexp_t * (bexp_t option) list (* program function application *)
| CnApp of
    string
    * bexp_t option list
    * btype_t  (* constant, predefined function application *)

and bconstant_t =
| CInt64 of int64 * ikind_t * string option
| CStr of string
| CWStr of int64 list
| CChr of char
| CReal of float * fkind_t * string option
| CEnum of bexp_t * string * string

and blval_t = blhost_t * boffset_t

and blhost_t =
| Var of varuse_t
| Mem of bexp_t

and boffset_t = 
| NoOffset
| Field of fielduse_t * boffset_t
| Index of bexp_t * boffset_t

and binit_t =
| SingleInit of bexp_t
| CompoundInit of btype_t * (boffset_t * binit_t) list

and binitinfo_t = binit_t option
  
and bblock_t = {
  battrs: b_attributes_t;
  bstmts: bstmt_t list
}
  
and bstmt_t = {
  labels: blabel_t list;
  skind: bstmtkind_t;
  sid: int;
  succs: int list;
  preds: int list 
}
  
and blabel_t =
| Label of string * b_location_t * bool
| Case of bexp_t * b_location_t
| CaseRange of bexp_t * bexp_t * b_location_t
| Default of b_location_t
    
and bstmtkind_t =
| Instr of binstr_t list
| Return of bexp_t option * b_location_t
| Goto of int * b_location_t
| ComputedGoto of bexp_t * b_location_t
| Break of b_location_t
| Continue of b_location_t
| If of bexp_t * bblock_t * bblock_t * b_location_t
| Switch of bexp_t * bblock_t * (int list) * b_location_t
| Loop of
    bblock_t
    * b_location_t
    * (int option)
    * (int option) (* continue stmt, break stmt *)
| Block of bblock_t
| TryFinally of bblock_t * bblock_t * b_location_t
| TryExcept of bblock_t * (binstr_t list * bexp_t) * bblock_t * b_location_t
    
and b_asm_output_t = string option * string * blval_t (* name, constraint, lval *)
  
and b_asm_input_t = string option * string * bexp_t (* name, constraint, bexp_t *)
  
and binstr_t =
| Set of blval_t * bexp_t * b_location_t
| Call of blval_t option * bexp_t * bexp_t list * b_location_t
| Asm of
    b_attributes_t
    * string list
    * b_asm_output_t list
    * b_asm_input_t list
    * string list
    * b_location_t
    
and b_location_t = {
  line: int ;
  file: string ;
  byte: int
}
  
and btypsig_t =
| TSArray of btypsig_t * int64 option * b_attribute_t list
| TSPtr of btypsig_t * b_attribute_t list
| TSComp of bool * string * b_attribute_t list
| TSFun of btypsig_t * btypsig_t list option * bool * b_attribute_t list
| TSEnum of string * b_attribute_t list
| TSBase of btype_t


type bcfundec_t = {
    bsvar: bvarinfo_t;
    bsformals: bvarinfo_t list;
    bslocals: bvarinfo_t list;
    bsbody: bblock_t
  }
    
type bglobal_t =
| GType of btypeinfo_t * b_location_t
| GCompTag of bcompinfo_t * b_location_t
| GCompTagDecl of bcompinfo_t * b_location_t
| GEnumTag of benuminfo_t * b_location_t
| GEnumTagDecl of benuminfo_t * b_location_t
| GVarDecl of bvarinfo_t * b_location_t
| GVar of bvarinfo_t * binitinfo_t * b_location_t
| GFun of bcfundec_t * b_location_t
| GAsm of string * b_location_t
| GPragma of b_attribute_t * b_location_t
| GText of string


type bcfile_t = {
    bfilename: string;
    bglobals: bglobal_t list
  }

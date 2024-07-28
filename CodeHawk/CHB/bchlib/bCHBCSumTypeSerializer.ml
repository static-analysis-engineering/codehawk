(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2024  Aarno Labs LLC

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
open CHPrettyUtil
open CHSumTypeSerializer

(* bchlib *)
open BCHBCTypes


module H = Hashtbl

exception BCHC_failure of pretty_t


let ikind_mfts: ikind_t mfts_int =
  mk_fn_mfts
    "ikind_t"
    [(IChar, "ichar");
     (ISChar, "ischar");
     (IUChar, "iuchar");
     (IWChar, "iwchar");
     (IBool, "ibool");
     (IInt, "iint");
     (IUInt, "iuint");
     (IShort, "ishort");
     (IUShort, "iushort");
     (ILong, "ilong");
     (IULong, "iulong");
     (ILongLong, "ilonglong");
     (IULongLong, "iulonglong");
     (IInt128, "int128_t");
     (IUInt128, "uint128_t")]
    (fun k ->
      match k with
      | INonStandard (true,i) -> "nt_" ^ (string_of_int i)
      | INonStandard (false,i) -> "nf_" ^ (string_of_int i)
      | _ -> raise (BCHC_failure (STR "Invalid ikind specifier")))
    (fun s ->
       try
         match nsplit '_' s with
         | ["nt"; n] -> INonStandard (true,int_of_string n)
         | ["nf"; n] -> INonStandard (false,int_of_string n)
         | _ ->
            raise
              (BCHC_failure (LBLOCK [STR "Invalid ikind specifier: "; STR s]))
       with
       | Failure _ ->
          raise
            (BCHC_failure
               (LBLOCK [STR "Invalid ikind specifier size: "; STR s])))


let fkind_mfts: fkind_t mfts_int =
  mk_mfts
    "fkind_t"
    [(FFloat, "float");
     (FDouble, "fdouble");
     (FLongDouble, "flongdouble");
     (FComplexFloat, "fcomplexfloat");
     (FComplexDouble, "fcomplexdouble");
     (FComplexLongDouble, "fcomplexlongdouble")]


let signedness_mfts: signedness_t mfts_int =
  mk_mfts
    "signedness_t"
    [(Signed, "s"); (Unsigned, "u"); (SignedNeutral, "n")]


let frepresentation_mfts: frepresentation_t mfts_int =
  mk_mfts  "frepresentation" [(FScalar,"s"); (FPacked,"p")]


let unop_mfts: unop_t mfts_int =
  mk_mfts
    "unop_t"  [(Neg, "neg"); (BNot, "bnot"); (LNot, "lnot")]

    
let binop_mfts: binop_t mfts_int =
  mk_mfts
  "binop_t"
  [(PlusA, "plusa");
   (PlusPI, "pluspi");
   (IndexPI, "indexpi");
   (MinusA, "minusa");
   (MinusPI, "minuspi");
   (MinusPP, "minuspp");
   (Mult, "mult");
   (Div, "div");
   (Mod, "mod");
   (Shiftlt, "shiftlt");
   (Shiftrt, "shiftrt");
   (Lt, "lt");
   (Gt, "gt");
   (Le, "le");
   (Ge, "ge");
   (Eq, "eq");
   (Ne, "ne");
   (BAnd, "band");
   (BXor, "bxor");
   (BOr, "bor");
   (LAnd, "land");
   (LOr, "lor")]


let storage_mfts: bstorage_t mfts_int =
  mk_mfts
    "bstorage_t"
    [(NoStorage,"n"); (Static,"s"); (Register,"r"); (Extern,"x")]


class typ_mcts_t:[btype_t] mfts_int =
object

  inherit [btype_t] mcts_t "btype_t"
  
  method !ts (t:btype_t) =
    match t with
    | TVoid _ -> "tvoid"
    | TInt _ -> "tint"
    | TFloat _ -> "tfloat"
    | TPtr _ -> "tptr"
    | TRef _ -> "tref"
    | THandle _ -> "thandle"
    | TArray _ -> "tarray"
    | TFun _ -> "tfun"
    | TNamed _ -> "tnamed"
    | TComp _ -> "tcomp"
    | TEnum _ -> "tenum"
    | TCppComp _ -> "tcppcomp"
    | TCppEnum _ -> "tcppenum"
    | TClass _ -> "tclass"
    | TBuiltin_va_list _ -> "tbuiltin-va-list"
    | TVarArg _ -> "tvararg"
    | TUnknown _ -> "tunknown"

  method !tags = [
      "tarray";
      "tbuiltin-va-list";
      "tclass";
      "tcomp";
      "tenum";
      "tfloat";
      "tfun";
      "thandle";
      "tint";
      "tnamed";
      "tptr";
      "tref";
      "tunknown";
      "tvoid"]                           

end

let typ_mcts: btype_t mfts_int = new typ_mcts_t


class tname_mcts_t: [tname_t] mfts_int =
object

  inherit [tname_t] mcts_t "tname_t"

  method !ts (t: tname_t) =
    match t with
    | SimpleName _ -> "s"
    | TemplatedName _ -> "t"

  method !tags = ["s"; "t"]

end

let tname_mcts: tname_t mfts_int = new tname_mcts_t


class exp_mcts_t:[bexp_t] mfts_int =
object

  inherit [bexp_t] mcts_t "bexp_t"

  method !ts (e: bexp_t) =
    match e with
    | Const _ -> "const"
    | Lval _ -> "lval"
    | SizeOf _ -> "sizeof"
    | Real _ -> "real"
    | Imag _ -> "imag"
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
    | FnApp _ -> "fnapp"
    | CnApp _ -> "cnapp"

  method !tags = [
      "addrof";
      "addroflabel";
      "alignof";
      "alignofe";
      "binop";
      "cnapp";
      "caste";
      "const";
      "fnapp";
      "lval";
      "question";
      "sizeof";
      "sizeofe";
      "startof";
      "unop"]

end

let exp_mcts: bexp_t mfts_int = new exp_mcts_t


class attrparam_mcts_t:[b_attrparam_t] mfts_int =
object

  inherit [b_attrparam_t] mcts_t "b_attrparam_t"

  method !ts (a: b_attrparam_t) =
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

  method !tags = [
      "aaddrof";
      "aalignof";
      "aalignofe";
      "aalignofs";
      "abinop";
      "acons";
      "adot";
      "aindex";
      "aint";
      "aquestion";
      "asizeof";
      "asizeofe";
      "asizeofs";
      "astar";
      "astr";
      "aunop"]

end

let attrparam_mcts: b_attrparam_t mfts_int = new attrparam_mcts_t


class constant_mcts_t:[bconstant_t] mfts_int =
object

  inherit [bconstant_t] mcts_t "bconstant_t"

  method !ts (c: bconstant_t) =
    match c with
    | CInt _ -> "int"
    | CStr _ -> "str"
    | CWStr _ -> "wstr"
    | CChr _ -> "chr"
    | CReal _ -> "real"
    | CEnum _ -> "enum"

  method !tags = ["chr"; "enum"; "int"; "real"; "str"; "wstr"]
               
end

let constant_mcts: bconstant_t mfts_int = new constant_mcts_t


class offset_mcts_t:[boffset_t] mfts_int =
object

  inherit [boffset_t] mcts_t "boffset_t"

  method !ts (o: boffset_t) =
    match o with
    | NoOffset -> "n"
    | Field _ -> "f"
    | Index _ -> "i"

  method !tags = ["f"; "i"; "n"]
               
end

let offset_mcts: boffset_t mfts_int = new offset_mcts_t
                                               

class typsig_mcts_t:[btypsig_t] mfts_int =
object

  inherit [btypsig_t] mcts_t "btypsig_t"

  method !ts (t: btypsig_t) =
    match t with
    | TSArray _ -> "tsarray"
    | TSPtr _ -> "tsptr"
    | TSComp _ -> "tscomp"
    | TSFun _ -> "tsfun"
    | TSEnum _ -> "tsenum"
    | TSBase _ -> "tsbase"

  method !tags = ["tsarray"; "tsbase"; "tscomp"; "tsenum"; "tsfun"; "tsptr"]
                
end

let typsig_mcts: btypsig_t mfts_int = new typsig_mcts_t
                                           

class label_mcts_t:[blabel_t] mfts_int =
object

  inherit [blabel_t] mcts_t "blabel_t"

  method !ts (l: blabel_t) =
    match l with
    | Label _ -> "label"
    | Case _ -> "case"
    | CaseRange _ -> "caserange"
    | Default _ -> "default"

  method !tags = ["case"; "caserange"; "default"; "label"]
                 
end

let label_mcts: blabel_t mfts_int = new label_mcts_t
                                          

class stmtkind_mcts_t:[bstmtkind_t] mfts_int =
object

  inherit [bstmtkind_t] mcts_t "bstmtkind_t"

  method !ts (s: bstmtkind_t) =
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

  method !tags = [
      "block";
      "break";
      "computedgoto";
      "continue";
      "goto";
      "if";
      "instr";
      "loop";
      "return";
      "switch";
      "tryexcept";
      "tryfinally"]
                   
end

let stmtkind_mcts: bstmtkind_t mfts_int = new stmtkind_mcts_t
                                        

class instr_mcts_t:[binstr_t] mfts_int =
object

  inherit [binstr_t] mcts_t "binstr_t"

  method !ts (i: binstr_t) =
    match i with
    | Set _ -> "set"
    | Call _ -> "call"
    | VarDecl _ -> "vardecl"
    | Asm _ -> "asm"

  method !tags = ["asm"; "call"; "set"; "vardecl"]
             
end

let instr_mcts: binstr_t mfts_int = new instr_mcts_t

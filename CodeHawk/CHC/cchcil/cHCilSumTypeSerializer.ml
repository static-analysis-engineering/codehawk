(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* chutil *)
open CHSumTypeSerializer

module H = Hashtbl


let ikind_mfts: ikind mfts_int =
  mk_mfts
    "ikind_t"
    [(IChar, "ichar");
     (ISChar, "ischar");
     (IUChar, "iuchar");
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


let fkind_mfts: fkind mfts_int =
  mk_mfts
    "fkind_t"
    [(FFloat, "float");
     (FDouble, "fdouble");
     (FLongDouble, "flongdouble");
     (FComplexFloat, "fcomplexfloat");
     (FComplexDouble, "fcomplexdouble");
     (FComplexLongDouble, "fcomplexlongdouble")]


let unop_mfts: unop mfts_int =
  mk_mfts
    "unop_t"  [(Neg, "neg"); (BNot, "bnot"); (LNot, "lnot")]


let binop_mfts: binop mfts_int =
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


let storage_mfts: storage mfts_int =
  mk_mfts
    "storage_t"
    [(NoStorage,"n"); (Static,"s"); (Register,"r"); (Extern,"x")]


class typ_mcts_t:[typ] mfts_int =
object

  inherit [typ] mcts_t "typ"
  
  method! ts (t: typ) =
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

  method! tags = [
      "tarray";
      "tbuiltin-va-list";
      "tcomp";
      "tenum";
      "tfloat";
      "tfun";
      "tint";
      "tnamed";
      "tptr";
      "tvoid"]                           

end


let typ_mcts: typ mfts_int = new typ_mcts_t


class exp_mcts_t:[exp] mfts_int =
object

  inherit [exp] mcts_t "exp"

  method! ts (e: exp) =
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

  method! tags = [
      "addrof";
      "addroflabel";
      "alignof";
      "alignofe";
      "binop";
      "caste";
      "const";
      "lval";
      "question";
      "sizeof";
      "sizeofe";
      "startof";
      "unop"]

end

let exp_mcts: exp mfts_int = new exp_mcts_t


class attrparam_mcts_t:[attrparam] mfts_int =
object

  inherit [attrparam] mcts_t "attrparam"

  method! ts (a: attrparam) =
    match a with
    | AInt _ -> "aint"
    | AStr _ -> "astr"
    | ACons _ -> "acons"
    | AAssign _ -> "aassign"
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

  method! tags = [
      "aaddrof";
      "aalignof";
      "aalignofe";
      "aalignofs";
      "aassign";
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

let attrparam_mcts: attrparam mfts_int = new attrparam_mcts_t

    

class constant_mcts_t:[constant] mfts_int =
object

  inherit [constant] mcts_t "constant"

  method! ts (c: constant) =
    match c with
    | CInt _ -> "int"
    | CStr _ -> "str"
    | CWStr _ -> "wstr"
    | CChr _ -> "chr"
    | CReal _ -> "real"
    | CEnum _ -> "enum"

  method! tags = ["chr"; "enum"; "int"; "real"; "str"; "wstr"]
               
end

let constant_mcts: constant mfts_int = new constant_mcts_t


class offset_mcts_t: [offset] mfts_int =
object

  inherit [offset] mcts_t "offset"

  method! ts (o: offset) =
    match o with
    | NoOffset -> "n"
    | Field _ -> "f"
    | Index _ -> "i"

  method! tags = ["f"; "i"; "n"]
               
end

let offset_mcts: offset mfts_int = new offset_mcts_t


class typsig_mcts_t:[typsig] mfts_int =
object

  inherit [typsig] mcts_t "typsig"

  method! ts (t: typsig) =
    match t with
    | TSArray _ -> "tsarray"
    | TSPtr _ -> "tsptr"
    | TSComp _ -> "tscomp"
    | TSFun _ -> "tsfun"
    | TSEnum _ -> "tsenum"
    | TSBase _ -> "tsbase"

  method! tags = ["tsarray"; "tsbase"; "tscomp"; "tsenum"; "tsfun"; "tsptr"]
                
end

let typsig_mcts: typsig mfts_int = new typsig_mcts_t
                                           

        
class label_mcts_t:[label] mfts_int =
object

  inherit [label] mcts_t "label"

  method! ts (l: label) =
    match l with
    | Label _ -> "label"
    | Case _ -> "case"
    | CaseRange _ -> "caserange"
    | Default _ -> "default"

  method! tags = ["case"; "caserange"; "default"; "label"]
                 
end

let label_mcts: label mfts_int = new label_mcts_t
                                          
 
class stmtkind_mcts_t:[stmtkind] mfts_int =
object

  inherit [stmtkind] mcts_t "stmtkind"

  method! ts (s: stmtkind) =
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

  method! tags = [
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

let stmtkind_mcts: stmtkind mfts_int = new stmtkind_mcts_t
                                        

class instr_mcts_t:[instr] mfts_int =
object

  inherit [instr] mcts_t "instr"

  method! ts (i: instr) =
    match i with
    | Set _ -> "set"
    | Call _ -> "call"
    | VarDecl _ -> "vardecl"
    | Asm _ -> "asm"

  method! tags = ["asm"; "call"; "set"; "vardecl"]
             
end

let instr_mcts: instr mfts_int = new instr_mcts_t


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

(* chlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHSumTypeSerializer

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHUtilities

module H = Hashtbl


let ikind_mfts: ikind mfts_int =
  mk_mfts
    "ikind"
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
     (IUInt128, "uint128_t")
    ]


let fkind_mfts: fkind mfts_int =
  mk_mfts
    "fkind"
    [(FFloat, "float");
     (FDouble, "fdouble");
     (FLongDouble, "flongdouble");
     (FComplexFloat, "fcomplexfloat");
     (FComplexDouble, "fcomplexdouble");
     (FComplexLongDouble, "fcomplexlongdouble")]


let unop_mfts: unop mfts_int =
  mk_mfts "unop"  [(Neg, "neg"); (BNot, "bnot"); (LNot, "lnot")]


let binop_mfts: binop mfts_int =
  mk_mfts
  "binop"
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


let storage_mfts:storage mfts_int =
  mk_fn_mfts
    "storage"
    [(NoStorage,"n"); (Static,"s"); (Register,"r"); (Extern,"x")]
    (fun s ->
      match s with
      | Opaque n -> "o_" ^ (string_of_int n)
      | _ ->
         raise (CCHFailure (STR "internal error in storage_mfts")))
    (fun s ->
      match nsplit '_' s with
      | ["o"; n] -> Opaque (int_of_string n)
      | _ ->
         raise (CCHFailure (LBLOCK [STR "Invalid storage specifier: "; STR s])))


class typ_mcts_t:[typ] mfts_int =
object

  inherit [typ] mcts_t "typ"

  method! ts (t:typ) =
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
      "tarray"; "tbuiltin-va-list"; "tcomp"; "tenum"; "tfloat"; "tfun";
      "tint"; "tnamed"; "tptr";  "tvoid"]

end

let typ_mcts: typ mfts_int = new typ_mcts_t


class exp_mcts_t:[exp] mfts_int =
object

  inherit [exp] mcts_t "exp"

  method! ts (e:exp) =
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
    | FnApp _ -> "fnapp"
    | CnApp _ -> "cnapp"

  method! tags = [
      "addrof"; "addroflabel"; "alignof"; "alignofe"; "binop";
      "cnapp"; "caste"; "const"; "fnapp"; "lval"; "question";
      "sizeof"; "sizeofe"; "startof"; "unop"]

end

let exp_mcts:exp mfts_int = new exp_mcts_t


class attrparam_mcts_t:[attrparam] mfts_int =
object

  inherit [attrparam] mcts_t "attrparam"

  method! ts (a:attrparam) =
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
    | AAssign _ -> "aassign"

  method! tags = [
      "aaddrof"; "aalignof"; "aalignofe"; "aalignofs"; "aassign";
      "abinop";
      "acons"; "adot"; "aindex"; "aint"; "aquestion"; "asizeof";
      "asizeofe"; "asizeofs"; "astar"; "astr"; "aunop"]

end

let attrparam_mcts: attrparam mfts_int = new attrparam_mcts_t

class constant_mcts_t:[constant] mfts_int =
object

  inherit [constant] mcts_t "constant"

  method! ts (c:constant) =
    match c with
    | CInt _ -> "int"
    | CStr _ -> "str"
    | CWStr _ -> "wstr"
    | CChr _ -> "chr"
    | CReal _ -> "real"
    | CEnum _ -> "enum"

  method! tags = [ "chr"; "enum"; "int"; "real"; "str"; "wstr"]

end

let constant_mcts: constant mfts_int = new constant_mcts_t


class offset_mcts_t:[offset] mfts_int =
object

  inherit [offset] mcts_t "offset"

  method! ts (o:offset) =
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

  method! ts (t:typsig) =
    match t with
    | TSArray _ -> "tsarray"
    | TSPtr _ -> "tsptr"
    | TSComp _ -> "tscomp"
    | TSFun _ -> "tsfun"
    | TSEnum _ -> "tsenum"
    | TSBase _ -> "tsbase"

  method! tags = ["tsarray"; "tsbase"; "tscomp"; "tsenum"; "tsfun"; "tsptr"]

end

let typsig_mcts:typsig mfts_int = new typsig_mcts_t


class label_mcts_t:[label] mfts_int =
object

  inherit [label] mcts_t "label"

  method! ts (l:label) =
    match l with
    | Label _ -> "label"
    | Case _ -> "case"
    | CaseRange _ -> "caserange"
    | Default _ -> "default"

  method! tags = ["case"; "caserange"; "default"; "label"]

end

let label_mcts:label mfts_int = new label_mcts_t


class stmtkind_mcts_t:[stmtkind] mfts_int =
object

  inherit [stmtkind] mcts_t "stmtkind"

  method! ts (s:stmtkind) =
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

  method! tags = [
      "block"; "break"; "computedgoto"; "continue"; "goto"; "if";
      "instr"; "loop";  "return"; "switch"; "tryexcept"; "tryfinally"]

end


let stmtkind_mcts:stmtkind mfts_int = new stmtkind_mcts_t

class instr_mcts_t:[instr] mfts_int =
object

  inherit [instr] mcts_t "instr"

  method! ts (i:instr) =
    match i with
    | Set _ -> "set"
    | Call _ -> "call"
    | Asm _ -> "asm"
    | VarDecl _ -> "vardecl"

  method! tags = ["asm"; "call"; "set"; "vardecl"]

end

let instr_mcts:instr mfts_int = new instr_mcts_t


class api_parameter_mcts_t: [api_parameter_t] mfts_int =
object

  inherit [api_parameter_t] mcts_t "api_parameter_t"

  method! ts (a:api_parameter_t) =
    match a with
    | ParFormal _ -> "pf"
    | ParGlobal _ -> "pg"

  method! tags = ["pf"; "pg"]

end


let api_parameter_mcts = new api_parameter_mcts_t


class s_offset_mcts_t: [s_offset_t] mfts_int =
object

  inherit [s_offset_t] mcts_t "s_offset_t"

  method! ts (s:s_offset_t) =
    match s with
    | ArgNoOffset -> "no"
    | ArgFieldOffset _ -> "fo"
    | ArgIndexOffset _ -> "io"

  method! tags = ["fo"; "io"; "no"]

end

let s_offset_mcts = new s_offset_mcts_t


class s_term_mcts_t: [s_term_t] mfts_int =
object

  inherit [s_term_t] mcts_t "s_term_t"

  method! ts (s:s_term_t) =
    match s with
    | ArgValue _ -> "av"
    | LocalVariable _ -> "lv"
    | ExternalState _ -> "es"
    | ReturnValue -> "rv"
    | NamedConstant _ -> "nc"
    | NumConstant _ -> "ic"
    | IndexSize _ -> "is"
    | ByteSize _ -> "bs"
    | ArgAddressedValue _ -> "aa"
    | ArgNullTerminatorPos _ -> "at"
    | ArgSizeOfType _ -> "st"
    | ArithmeticExpr _ -> "ax"
    | FormattedOutputSize _ -> "fs"
    | Region _ -> "rg"
    | RuntimeValue -> "rt"
    | ChoiceValue _ -> "cv"

  method! tags = [
      "aa"; "at"; "av"; "ax"; "bs"; "cv"; "es"; "fs"; "ic"; "is"; "lv";
      "nc"; "rg"; "rt"; "rv"; "st"]

end

let s_term_mcts = new s_term_mcts_t


class xpredicate_mcts_t: [xpredicate_t] mfts_int =
object

  inherit [xpredicate_t] mcts_t "xpredicate"

  method! ts (p:xpredicate_t) =
    match p with
    | XAllocationBase _ -> "ab"
    | XBlockWrite _ -> "bw"
    | XBuffer _ -> "b"
    | XConfined _ -> "cf"
    | XConstTerm _ -> "c"
    | XControlledResource _ -> "cr"
    | XExternalStateValue _ -> "esv"
    | XFormattedInput _ -> "fi"
    | XFalse -> "f"
    | XFreed _ -> "fr"
    | XFunctional -> "fn"
    | XGlobalAddress _ -> "ga"
    | XHeapAddress _ -> "ha"
    | XInitialized _ -> "i"
    | XInitializedRange _ -> "ir"
    | XInitializesExternalState _ -> "ies"
    | XInputFormatString _ -> "ifs"
    | XInvalidated _ -> "iv"
    | XNewMemory _ -> "nm"
    | XNoOverlap _ -> "no"
    | XNotNull _ -> "nn"
    | XNotZero _ -> "nz"
    | XNonNegative _ -> "nng"
    | XNull _ -> "null"
    | XNullTerminated _ -> "nt"
    | XOutputFormatString _ -> "ofs"
    | XPreservesAllMemory -> "prm"
    | XPreservesAllMemoryX _ -> "prmx"
    | XPreservesMemory _ -> "pr"
    | XPreservesValue _ -> "pv"
    | XPreservesNullTermination -> "prn"
    | XPreservesValidity _ -> "prv"
    | XRelationalExpr _ -> "x"
    | XRepositioned _ -> "rep"
    | XRevBuffer _ -> "rb"
    | XStackAddress _ -> "sa"
    | XTainted _ -> "tt"
    | XUniquePointer _ -> "up"
    | XValidMem _ -> "vm"
    | XPolicyPre _ -> "pop"
    | XPolicyValue _ -> "pov"
    | XPolicyTransition _ -> "pox"

  method! tags = [
      "ab"; "b"; "bw"; "c"; "cf"; "cr"; "esv"; "f"; "fi"; "fn"; "fr"; "ga";
      "ha"; "i"; "ies"; "ifs"; "ir"; "iv"; "nm"; "nn"; "no"; "nz"; "nng";
      "nt"; "null"; "ofs"; "pop"; "pov"; "pox";  "pr"; "prm";
      "prmx"; "prn"; "prv"; "pv"; "rb"; "rep"; "sa"; "tt"; "up";
      "vm"; "x"]

end

let xpredicate_mcts = new xpredicate_mcts_t
